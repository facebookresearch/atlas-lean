/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.SymmetricKey.PRF
public import CSLibExt.Crypto.Hash.Birthday
public import CSLibExt.Crypto.Framework.Asymptotic
public import CSLibExt.Crypto.Framework.LazySampling

/-!
# Pseudorandom permutations and the switching lemma

A keyed permutation `F : K → Equiv.Perm X` is a **pseudorandom permutation** (Katz and Lindell,
Section 3.5.1) when no distinguisher with oracle access tells `F k`, for a uniform key `k`,
from a uniformly random permutation of `X`.

* `prpReal F D`, `prpRand D : PMF Bool` and `prpAdvantage F D`: the PRP experiment, in the shape
  of `Cslib.Crypto.PRF.prfReal`, `prfRand` (adaptive distinguishers `D : S → OracleComp X X Bool`
  with uniform coins `s : S`). `prpReal_eq_prfReal`: the real worlds of the two experiments
  coincide.

**The switching lemma** (Bellare and Rogaway, Lemma 1; Boneh and Shoup, Theorem 4.4): a random
permutation and a random function are indistinguishable to `q` queries up to the birthday term.
* `abs_prfRand_sub_prpRand_le` (exact form): for a distinguisher making at most `q` queries,
  `|Pr[D^f = 1] - Pr[D^π = 1]| ≤ collisionProb X q`, the probability that `q` uniform samples
  from `X` collide (`CSLibExt.Crypto.Hash.Birthday`).
* `abs_prfRand_sub_prpRand_le_birthday`: hence at most `q (q - 1) / (2 |X|)` by the birthday
  bound `Cslib.Crypto.Birthday.collisionProb_le`.
* `prfAdvantage_le` (**a PRP is a PRF**; Katz and Lindell, Section 3.5.1, the proposition that a
  pseudorandom permutation with input length at least `n` is a pseudorandom function):
  `prfAdvantage F D ≤ prpAdvantage F D + collisionProb X q`.
* `PRPSecure F Admissible`: asymptotic PRP security relative to a caller-supplied class of
  distinguisher families. It is an abstract relative-indistinguishability predicate, not Katz and
  Lindell's definition verbatim: the source requires `F` to be an *efficient*, length-preserving
  keyed permutation (`F_k` and `F_k⁻¹` computable in deterministic polynomial time) and
  quantifies over probabilistic polynomial-time distinguishers. Neither efficiency condition on
  `F` is imposed here, so a noncomputable family can satisfy `PRPSecure`; the restriction on
  distinguishers is whatever `Admissible` encodes (the framework has no polynomial-time model for
  oracle algorithms, see "What is deferred" in `CSLibExt.Crypto.Framework.Asymptotic`).
* `prfSecure_of_prpSecure`: the asymptotic form, when the birthday term is negligible for every
  polynomial number of queries. Its conclusion is the PRF API's notion
  `Cslib.Crypto.PRF.PRFSecure` (relative in the same sense); this file defines only `PRPSecure`.

**Proof.** The information-theoretic step is
`Cslib.Crypto.Framework.LazySampling.switching_lemma`, for one deterministic adaptive query tree.
`abs_prfRand_sub_prpRand_le` applies it to `D s` for each coin value `s` and averages over the
uniform coins.

**What is deferred.** Strong pseudorandom permutations (Katz and Lindell, Definition 3.28, with an
oracle for the inverse) are not modelled. Wave 2: migrate to Framework. The PRP game is not part of
`CSLibExt.Crypto.Framework`; it is defined here in the shape of `Cslib.Crypto.PRF` so that the
switching lemma composes with `Cslib.Crypto.PRF.prfAdvantage`.

## References

* J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014,
  Section 3.5.1 and Appendix A.4.
* M. Bellare and P. Rogaway, *The security of triple encryption and a framework for code-based
  game-playing proofs*, EUROCRYPT 2006, Lemma 1.
* D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6, Theorem 4.4.
-/

@[expose] public section

namespace Cslib.Crypto.PRP

open Finset Cslib.Crypto.Framework
open Cslib.Crypto.PRF (OracleComp)
open Cslib.Crypto.Framework.OracleComp (run run_congr queries)

/-! ### The PRP experiment -/

section Game

variable {K X S : Type*} [Fintype K] [Nonempty K] [Fintype X] [DecidableEq X] [Fintype S]
  [Nonempty S]

/-- The real world: the distinguisher with uniform coins queries `F k` for a uniform key `k`. -/
noncomputable def prpReal (F : K → Equiv.Perm X) (D : S → OracleComp X X Bool) : PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype (K × S)).map fun ω => (D ω.2).run ⇑(F ω.1)

/-- The random world: the distinguisher queries a uniformly random permutation of `X`. -/
noncomputable def prpRand (D : S → OracleComp X X Bool) : PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype (Equiv.Perm X × S)).map fun ω : Equiv.Perm X × S =>
    (D ω.2).run ⇑ω.1

/-- The PRP advantage `|Pr[D^{F_k} = 1] - Pr[D^π = 1]|` (Katz and Lindell, Section 3.5.1). -/
noncomputable def prpAdvantage (F : K → Equiv.Perm X) (D : S → OracleComp X X Bool) : ℝ :=
  advantage (prpReal F D) (prpRand D)

omit [Fintype X] [DecidableEq X] in
/-- The real world of the PRP experiment is the real world of the PRF experiment for the keyed
function `fun k => F k`. -/
theorem prpReal_eq_prfReal (F : K → Equiv.Perm X) (D : S → OracleComp X X Bool) :
    prpReal F D = Cslib.Crypto.PRF.prfReal (fun k => ⇑(F k)) D := rfl

end Game

/-! ### The switching lemma -/

section Switching

variable {S : Type*} [Fintype S] [Nonempty S]

/-- The success probability of a uniform-coins experiment is the average over the coins `s` of
the success probabilities of the experiments with `s` fixed. -/
private theorem winProb_map_uniform_prod {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (g : Ω → S → Bool) :
    winProb ((Cslib.Probability.PMF.uniformOfFintype (Ω × S)).map fun ω => g ω.1 ω.2) =
      (∑ s, winProb ((Cslib.Probability.PMF.uniformOfFintype Ω).map fun ω => g ω s)) /
        Fintype.card S := by
  classical
  simp only [winProb_map_uniform]
  rw [Fintype.card_prod, Nat.cast_mul, ← sum_div, div_div]
  congr 1
  rw [card_filter, Fintype.sum_prod_type_right]
  push_cast
  refine sum_congr rfl fun s _ => ?_
  rw [card_filter]
  push_cast
  rfl

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]

/-- **The switching lemma** (Bellare and Rogaway, Lemma 1; Boneh and Shoup, Theorem 4.4): a
distinguisher with uniform coins making at most `q` queries tells a random function from a random
permutation with advantage at most `collisionProb X q`. For each fixed coin value this is
`Cslib.Crypto.Framework.LazySampling.switching_lemma`; the advantage over uniform coins is the
average of those advantages. -/
theorem abs_prfRand_sub_prpRand_le {q : ℕ} (D : S → OracleComp X X Bool)
    (hD : ∀ s, FreeM.IsQueryBounded q (D s)) :
    advantage (Cslib.Crypto.PRF.prfRand D) (prpRand D) ≤
      Cslib.Crypto.Birthday.collisionProb X q := by
  have hS : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hrand : winProb (Cslib.Crypto.PRF.prfRand D) =
      (∑ s, winProb ((Cslib.Probability.PMF.uniformOfFintype (X → X)).map fun f =>
        (D s).run f)) / Fintype.card S :=
    winProb_map_uniform_prod fun f s => (D s).run f
  have hperm : winProb (prpRand D) =
      (∑ s, winProb ((Cslib.Probability.PMF.uniformOfFintype (Equiv.Perm X)).map
        fun π : Equiv.Perm X => (D s).run ⇑π)) / Fintype.card S :=
    winProb_map_uniform_prod fun (π : Equiv.Perm X) s => (D s).run ⇑π
  rw [advantage, hrand, hperm, ← sub_div, ← sum_sub_distrib, abs_div, abs_of_pos hS,
    div_le_iff₀ hS]
  calc |∑ s, (winProb ((Cslib.Probability.PMF.uniformOfFintype (X → X)).map fun f =>
          (D s).run f) - winProb ((Cslib.Probability.PMF.uniformOfFintype (Equiv.Perm X)).map
          fun π : Equiv.Perm X => (D s).run ⇑π))|
      ≤ ∑ s, |winProb ((Cslib.Probability.PMF.uniformOfFintype (X → X)).map fun f =>
          (D s).run f) - winProb ((Cslib.Probability.PMF.uniformOfFintype (Equiv.Perm X)).map
          fun π : Equiv.Perm X => (D s).run ⇑π)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s : S, Cslib.Crypto.Birthday.collisionProb X q :=
        sum_le_sum fun s _ => LazySampling.switching_lemma (D s) (hD s)
    _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul, mul_comm]

/-- **The switching lemma, birthday form**: the advantage is at most `q (q - 1) / (2 |X|)`. -/
theorem abs_prfRand_sub_prpRand_le_birthday {q : ℕ} (D : S → OracleComp X X Bool)
    (hD : ∀ s, FreeM.IsQueryBounded q (D s)) :
    advantage (Cslib.Crypto.PRF.prfRand D) (prpRand D) ≤ q * (q - 1) / (2 * Fintype.card X) :=
  (abs_prfRand_sub_prpRand_le D hD).trans (Cslib.Crypto.Birthday.collisionProb_le X q)

variable {K : Type*} [Fintype K] [Nonempty K]

/-- **A pseudorandom permutation is a pseudorandom function** (Katz and Lindell, Section 3.5.1),
in concrete form: for a distinguisher making at most `q` queries, its PRF advantage against
`fun k => F k` is at most its PRP advantage against `F` plus the collision probability of `q`
uniform samples from `X` (at most `q (q - 1) / (2 |X|)`, `collisionProb_le`). -/
theorem prfAdvantage_le {q : ℕ} (F : K → Equiv.Perm X) (D : S → OracleComp X X Bool)
    (hD : ∀ s, FreeM.IsQueryBounded q (D s)) :
    Cslib.Crypto.PRF.prfAdvantage (fun k => ⇑(F k)) D ≤
      prpAdvantage F D + Cslib.Crypto.Birthday.collisionProb X q := by
  have h := advantage_triangle (prpReal F D) (prpRand D) (Cslib.Crypto.PRF.prfRand D)
  rw [advantage_comm (prpRand D)] at h
  exact (le_of_eq rfl).trans (h.trans (add_le_add le_rfl (abs_prfRand_sub_prpRand_le D hD)))

end Switching

/-! ### Asymptotic form -/

/-- **Asymptotic PRP security relative to `Admissible`** of a family of keyed permutations
`F n : K n → Perm (X n)`: every admissible family of distinguishers with coins in `S n` has
negligible `prpAdvantage` (the indistinguishability condition of Katz and Lindell, Section 3.5.1,
with the admissible class as a parameter).

This is an abstract relative-indistinguishability predicate. The source conditions it omits are
recorded here: Katz and Lindell require `F` to be an efficient, length-preserving keyed
permutation (`F_k` and `F_k⁻¹` computable in deterministic polynomial time) and quantify over
probabilistic polynomial-time distinguishers. Nothing here constrains how `F` is computed, so a
noncomputable family can satisfy `PRPSecure`; any restriction on distinguishers must be supplied
through `Admissible`. -/
def PRPSecure {K X S : ℕ → Type*} [∀ n, Fintype (K n)] [∀ n, Nonempty (K n)]
    [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)] [∀ n, Fintype (S n)] [∀ n, Nonempty (S n)]
    (F : (n : ℕ) → K n → Equiv.Perm (X n))
    (Admissible : ((n : ℕ) → S n → OracleComp (X n) (X n) Bool) → Prop) : Prop :=
  AsymptoticallySecure (fun n D => prpAdvantage (F n) D) Admissible

/-- **A PRP family is a PRF family** (Katz and Lindell, Section 3.5.1): if every admissible
distinguisher family makes polynomially many queries and the birthday term
`collisionProb (X n) (p n)` is negligible for every polynomial `p` (e.g. `|X n| = 2 ^ n`), then
PRP security implies PRF security. -/
theorem prfSecure_of_prpSecure {K X S : ℕ → Type*} [∀ n, Fintype (K n)] [∀ n, Nonempty (K n)]
    [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)] [∀ n, Nonempty (X n)] [∀ n, Fintype (S n)]
    [∀ n, Nonempty (S n)] (F : (n : ℕ) → K n → Equiv.Perm (X n))
    (Admissible : ((n : ℕ) → S n → OracleComp (X n) (X n) Bool) → Prop)
    (hpoly : ∀ D, Admissible D →
      ∃ p : Polynomial ℕ, ∀ n s, FreeM.IsQueryBounded (p.eval n) (D n s))
    (hbday : ∀ p : Polynomial ℕ,
      NegligibleAdv fun n => Cslib.Crypto.Birthday.collisionProb (X n) (p.eval n))
    (hF : PRPSecure F Admissible) :
    Cslib.Crypto.PRF.PRFSecure (fun n k => ⇑(F n k)) Admissible := by
  intro D hD
  obtain ⟨p, hp⟩ := hpoly D hD
  exact ((hF D hD).add (hbday p)).mono fun n => prfAdvantage_le (F n) (D n) (hp n)

end Cslib.Crypto.PRP
