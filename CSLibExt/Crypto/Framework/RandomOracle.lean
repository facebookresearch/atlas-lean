/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.LazySampling

/-!
# The random-oracle model

In the random-oracle model (Katz and Lindell, Section 5.5) every party has oracle access to a
uniformly random function `H : D → Rng`. A random function on a large domain cannot be sampled up
front, so it is simulated **lazily**: the oracle keeps a table of the queries answered so far,
answers a repeated query from the table, and answers a fresh query with a fresh uniform value,
which it records (Katz and Lindell, Section 5.5.1).

**One implementation.** The lazy random oracle is the lazy random function of
`CSLibExt.Crypto.Framework.LazySampling`: its `Table`, `Extends`, `runState`, `rfStep` and `lazyRF`
are used here unchanged, so every lemma of that file applies directly. The facts the
random-oracle model relies on all live there:
* `LazySampling.runState_bind`: `runState` turns sequential composition into `PMF.bind`.
* Consistency: `LazySampling.rfStep_of_some` (a recorded query is answered from the table,
  deterministically), `LazySampling.mem_support_rfStep` (the answer is recorded, and the table
  only grows), `LazySampling.extends_of_mem_support_runState` (along a whole run the table only
  grows), and `LazySampling.lazyRF_query_query` (querying `x` twice is the same as querying it
  once and reusing the answer).
* Fresh-answer uniformity: `LazySampling.rfStep_of_none` and `LazySampling.rfStep_map_fst_of_none`
  (a fresh query is answered uniformly), and the adaptive lazy = eager theorem
  `LazySampling.lazyRF_map_fst`.

This file adds the random-oracle experiments built on that API.
* `RandomOracle.map_fst_lazyRF_queryVec`: the answers to `n` pairwise distinct fresh queries are
  independent and uniform, i.e. a uniform function `Fin n → Rng`.
* `RandomOracle.eval c` runs `c` against the lazy random oracle from the empty table and returns
  its output distribution.
* The collision bound: `collisionExp xs` queries the points `xs` and outputs whether two answers
  coincide. For pairwise distinct points (`Function.Injective xs`), `collisionExp_eq`: it is the
  birthday experiment `Cslib.Crypto.Birthday.collisionGame Rng q`, so (`winProb_collisionExp_le`)
  its probability is at most `q (q - 1) / (2 |Rng|)`. This slightly strengthens, and implies,
  Katz and Lindell's Lemma A.15, which states the bound `q ^ 2 / (2 |Rng|)`.

Applications (Fiat–Shamir, hash-and-sign, OAEP) are not built here.

## References

* J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014,
  Section 5.5 and Appendix A.4.
-/

@[expose] public section

namespace Cslib.Crypto.Framework

open FreeM OracleComp

namespace RandomOracle

open LazySampling

variable {D Rng : Type*} [DecidableEq D] [Fintype Rng] [Nonempty Rng]

/-- The output distribution of an oracle computation in the random-oracle model (Katz and Lindell,
Section 5.5.1): run it against the lazy random function `LazySampling.lazyRF` from the empty
table. -/
noncomputable def eval {α : Type*} (c : OracleComp D Rng α) : PMF α :=
  (lazyRF c Table.empty).map Prod.fst

/-! ### Distinct queries and the collision bound -/

/-- Query the points `xs 0, …, xs (n - 1)` in order and return the answers. -/
def queryVec : (n : ℕ) → (Fin n → D) → OracleComp D Rng (Fin n → Rng)
  | 0, _ => .pure fun i => i.elim0
  | n + 1, xs => .liftBind (xs 0) fun y =>
      PFunctor.FreeM.bind (queryVec n (Fin.tail xs)) fun ys => .pure (Fin.cons y ys)

/-- **Distinct fresh queries get independent uniform answers**: if the points `xs` are pairwise
distinct and not yet in the table, the vector of answers is a uniform function `Fin n → Rng`. -/
theorem map_fst_lazyRF_queryVec :
    ∀ (n : ℕ) (xs : Fin n → D) (T : Table D Rng), Function.Injective xs →
      (∀ i, T (xs i) = none) →
        (lazyRF (queryVec n xs) T).map Prod.fst =
          Cslib.Probability.PMF.uniformOfFintype (Fin n → Rng)
  | 0, _, _, _, _ => by
    rw [Cslib.Probability.PMF.uniformOfFintype_unique]
    exact (PMF.pure_map _ _).trans (congrArg PMF.pure (Subsingleton.elim _ _))
  | n + 1, xs, T, hxs, hT => by
    have ih : ∀ y : Rng, (lazyRF (queryVec n (Fin.tail xs))
        (Function.update T (xs 0) (some y))).map Prod.fst =
          Cslib.Probability.PMF.uniformOfFintype (Fin n → Rng) := by
      intro y
      refine map_fst_lazyRF_queryVec n _ _ (hxs.comp (Fin.succ_injective n)) fun i => ?_
      change Function.update T (xs 0) (some y) (xs i.succ) = none
      rw [Function.update_of_ne (fun h => Fin.succ_ne_zero i (hxs h)), hT]
    simp only [queryVec, lazyRF, runState, rfStep_of_none (hT 0), PMF.bind_map,
      Function.comp_def, runState_bind] at ih ⊢
    simp only [PMF.map_bind, PMF.pure_map]
    rw [Cslib.Probability.PMF.uniformOfFintype_fin_succ]
    congr 1
    funext y
    rw [← ih y, PMF.map_comp]
    rfl

open Classical in
/-- The collision experiment in the random-oracle model: query the `q` points `xs` in order and
output whether two of the answers coincide. The points need not be distinct; repeated points get
equal answers, and the results below assume `Function.Injective xs`. -/
noncomputable def collisionExp {q : ℕ} (xs : Fin q → D) : PMF Bool :=
  (eval (Rng := Rng) (queryVec q xs)).map fun ys => !decide (Function.Injective ys)

/-- The collision experiment on distinct points is the birthday experiment of
`Cslib.Crypto.Birthday` on the range. -/
theorem collisionExp_eq {q : ℕ} {xs : Fin q → D} (hxs : Function.Injective xs) :
    collisionExp (Rng := Rng) xs = Cslib.Crypto.Birthday.collisionGame Rng q := by
  rw [collisionExp, eval, map_fst_lazyRF_queryVec q xs _ hxs fun _ => rfl]
  rfl

/-- **The collision bound in the random-oracle model**: among the answers to `q` pairwise distinct
queries, two coincide with probability at most `q (q - 1) / (2 |Rng|)`. This slightly strengthens,
and implies, Katz and Lindell's Lemma A.15, which states the bound `q ^ 2 / (2 |Rng|)`. -/
theorem winProb_collisionExp_le {q : ℕ} {xs : Fin q → D} (hxs : Function.Injective xs) :
    winProb (collisionExp (Rng := Rng) xs) ≤ q * (q - 1) / (2 * Fintype.card Rng) := by
  rw [winProb, collisionExp_eq hxs]
  exact Cslib.Crypto.Birthday.collisionProb_le Rng q

end RandomOracle

end Cslib.Crypto.Framework
