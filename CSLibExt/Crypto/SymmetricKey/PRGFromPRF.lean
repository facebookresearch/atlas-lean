/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.SymmetricKey.PRF
public import CSLibExt.Crypto.SymmetricKey.PRG
public import CSLibExt.Crypto.Framework.RandomOracle

/-!
# Pseudorandom generators from pseudorandom functions

Let `F : K → X → Y` be a keyed function and `x : Fin n → X` a list of points. The generator
`prgOfPRF F x : K → (Fin n → Y)` maps a key `k` to `(F k (x 0), …, F k (x (n - 1)))` (Boneh and
Shoup, Section 4.4.4).

* `prgOfPRFReduction x A` is the PRF distinguisher built from a PRG distinguisher `A`: with `A`'s
  coins `r` it queries its oracle at `x 0, …, x (n - 1)` (`RandomOracle.queryVec`) and outputs
  `A`'s guess on the answers with coins `r`.
* `prgAdvantage_prgOfPRF_eq` (Boneh and Shoup, Theorem 4.8): if the points are distinct and `A`'s
  coins are uniform on a finite type, the reduction asks exactly the `n` queries `x 0, …, x (n - 1)`
  against every oracle, outputs `A`'s guess on the answers, and its PRF advantage against `F` is
  the PRG advantage of `A` against `prgOfPRF F x`. With the oracle `F k` the reduction shows `A`
  the string `prgOfPRF F x k`. With a uniformly random function the answers at distinct points
  are uniform (`LazySampling.lazyRF_map_fst` and `RandomOracle.map_fst_lazyRF_queryVec`), so it
  shows `A` a uniform string.
* `prgSecure_prgOfPRF`: the asymptotic form. Suppose that the points are distinct at every
  security parameter, that there are fewer keys than outputs, that every admissible PRG
  distinguisher family draws its coins uniformly, and that the family of keyed functions is
  `PRFSecure` against a class of distinguisher families containing the reductions. Then the
  family of generators is `PRGSecure`.

**Running time and coins.** `OracleComp` has no running time, so Boneh and Shoup's condition that
the reduction is an *elementary wrapper* around `A` (about the running time of `A`) is rendered
by the form of the reduction: besides its `n` queries it runs `A`'s guess once, on the answers,
with `A`'s own coins. The PRF distinguishers of `Cslib.Crypto.PRF.prfAdvantage` draw their coins
uniformly from a finite type and the reduction uses `A`'s coins as its own, which is why `A`'s
coins are taken uniform on a finite type, as a probabilistic algorithm's are. An equality needs
some such hypothesis: the coins of a `Distinguisher` may have any distribution, so a PRG advantage
can be irrational, whereas every PRF advantage is rational.

**Expansion.** The equality of advantages needs no relation between `|K|` and `|Y| ^ n`;
`|K| < |Y| ^ n` only makes the generator expand, which `PRGSecure` requires (following Katz and
Lindell), and it is a hypothesis of `prgSecure_prgOfPRF` alone. Boneh and Shoup's Theorem 4.8 has
no such hypothesis, and their Definition 3.1 of a secure PRG does not require expansion.

## References

* D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.4, 2017,
  Section 4.4.4, Theorem 4.8.
-/

@[expose] public section

namespace Cslib.Crypto.PRG

open Cslib.Crypto.Framework

/-! ### The generator and the reduction -/

section Construction

variable {K X Y R : Type*} {n : ℕ}

/-- **The generator of a keyed function at fixed points.** Let $F : K \to X \to Y$ be a keyed
function and let $x_1, \dots, x_n \in X$. The generator $G : K \to Y^n$ maps a key $k$ to
$G(k) = (F(k, x_1), \dots, F(k, x_n))$. -/
def prgOfPRF (F : K → X → Y) (x : Fin n → X) (k : K) : Fin n → Y := fun i => F k (x i)

/-- **The PRF distinguisher built from a PRG distinguisher.** Let $x_1, \dots, x_n \in X$ and let
$A$ be a distinguisher for strings in $Y^n$ with coins in $R$. With coins $r \in R$ and with oracle
access to a function $O : X \to Y$, the distinguisher queries $O$ at $x_1, \dots, x_n$, in this
order, and outputs the guess of $A$ on $(O(x_1), \dots, O(x_n))$ with coins $r$. -/
def prgOfPRFReduction (x : Fin n → X) (A : Distinguisher (Fin n → Y) R) (r : R) :
    OracleComp X Y Bool :=
  PFunctor.FreeM.bind (RandomOracle.queryVec n x) fun ys => OracleComp.done (A.guess ys r)

private theorem queries_bind {α β : Type*} (O : X → Y) (g : α → OracleComp X Y β) :
    ∀ c : OracleComp X Y α,
      OracleComp.queries O (PFunctor.FreeM.bind c g) = c.queries O ++ (g (c.run O)).queries O
  | .pure _ => rfl
  | .liftBind x k => by
    change x :: OracleComp.queries O (PFunctor.FreeM.bind (k (O x)) g) = x :: _
    rw [queries_bind O g (k (O x))]
    rfl

private theorem run_queryVec (O : X → Y) :
    ∀ (n : ℕ) (x : Fin n → X), (RandomOracle.queryVec n x).run O = fun i => O (x i)
  | 0, _ => funext fun i => i.elim0
  | n + 1, x => by
    change OracleComp.run O (PFunctor.FreeM.bind (RandomOracle.queryVec n (Fin.tail x))
      fun ys => .pure (Fin.cons (O (x 0)) ys) : OracleComp X Y (Fin (n + 1) → Y)) = _
    rw [OracleComp.run_bind, run_queryVec O n (Fin.tail x)]
    exact Fin.cons_self_tail fun i => O (x i)

private theorem queries_queryVec (O : X → Y) :
    ∀ (n : ℕ) (x : Fin n → X), (RandomOracle.queryVec n x).queries O = List.ofFn x
  | 0, _ => rfl
  | n + 1, x => by
    change x 0 :: OracleComp.queries O (PFunctor.FreeM.bind (RandomOracle.queryVec n (Fin.tail x))
      fun ys => .pure (Fin.cons (O (x 0)) ys) : OracleComp X Y (Fin (n + 1) → Y)) = _
    rw [queries_bind, queries_queryVec O n (Fin.tail x), List.ofFn_succ]
    exact congrArg _ (List.append_nil _)

theorem queries_prgOfPRFReduction (x : Fin n → X) (A : Distinguisher (Fin n → Y) R) (r : R)
    (O : X → Y) : (prgOfPRFReduction x A r).queries O = List.ofFn x := by
  rw [prgOfPRFReduction, queries_bind, queries_queryVec]
  exact List.append_nil _

theorem run_prgOfPRFReduction (x : Fin n → X) (A : Distinguisher (Fin n → Y) R) (r : R)
    (O : X → Y) : (prgOfPRFReduction x A r).run O = A.guess (fun i => O (x i)) r := by
  rw [prgOfPRFReduction, OracleComp.run_bind, run_queryVec]
  rfl

end Construction

/-! ### The reduction is exact -/

section Reduction

variable {K X Y R : Type*} [Fintype K] [Nonempty K] [Fintype X] [DecidableEq X] [Fintype Y]
  [Nonempty Y] [Fintype R] [Nonempty R] {n : ℕ}

-- A uniformly random function evaluated at distinct points is uniform.
private theorem uniformOfFintype_map_eval {x : Fin n → X} (hx : Function.Injective x) :
    (Cslib.Probability.PMF.uniformOfFintype (X → Y)).map (fun f i => f (x i)) =
      Cslib.Probability.PMF.uniformOfFintype (Fin n → Y) := by
  have h := LazySampling.lazyRF_map_fst (Y := Y) (RandomOracle.queryVec n x)
  rw [RandomOracle.map_fst_lazyRF_queryVec n x _ hx fun _ => rfl] at h
  rw [h]
  exact congrArg (PMF.map · _) (funext fun f => (run_queryVec f n x).symm)

/-- **Pseudorandom generators from pseudorandom functions.** Let $K$, $X$, $Y$ and $R$ be finite
sets with $K$, $Y$ and $R$ nonempty, let $F : K \to X \to Y$ be a keyed function, let
$x_1, \dots, x_n \in X$ be distinct, and let $G : K \to Y^n$ be the generator
$G(k) = (F(k, x_1), \dots, F(k, x_n))$. Let $A$ be a distinguisher for strings in $Y^n$ whose
coins are uniform on $R$, and let $B$ be the PRF distinguisher with coins in $R$ that, with coins
$r$ and oracle $O : X \to Y$, queries $O$ at $x_1, \dots, x_n$, in this order, and outputs the
guess of $A$ on $(O(x_1), \dots, O(x_n))$ with coins $r$. Then, for all coins $r$ and every
oracle $O$, $B$ asks exactly the $n$ queries $x_1, \dots, x_n$, in this order, and outputs the
guess of $A$ on $(O(x_1), \dots, O(x_n))$ with coins $r$; and the PRG advantage of $A$ against $G$
equals the PRF advantage of $B$ against $F$.

This is the concrete form of Boneh and Shoup, Theorem 4.8. There is no running-time model: their
condition that $B$ is an elementary wrapper around $A$ is rendered by the form of $B$, which
besides its $n$ queries runs $A$ once, on the answers, with $A$'s coins. PRF distinguishers draw
their coins uniformly from a finite set and $B$ uses $A$'s coins as its own, which is why $A$'s
coins are taken uniform, as a probabilistic algorithm's are. An equality needs some such
hypothesis: PRG distinguishers may have coins with any distribution, so a PRG advantage can be
irrational, whereas every PRF advantage is rational. The equality does not need $|K| < |Y|^n$,
which only makes $G$ expand. That condition comes from the asymptotic PRG security `PRGSecure`,
which requires expansion, following Katz and Lindell; Boneh and Shoup's Theorem 4.8 has no such
hypothesis, and their Definition 3.1 of a secure PRG does not require expansion. -/
theorem prgAdvantage_prgOfPRF_eq (F : K → X → Y) {x : Fin n → X} (hx : Function.Injective x)
    (A : Distinguisher (Fin n → Y) R) (hA : A.coins = Cslib.Probability.PMF.uniformOfFintype R) :
    (∀ r O, (prgOfPRFReduction x A r).queries O = List.ofFn x) ∧
      (∀ r O, (prgOfPRFReduction x A r).run O = A.guess (fun i => O (x i)) r) ∧
      prgAdvantage (prgOfPRF F x) A = PRF.prfAdvantage F (prgOfPRFReduction x A) := by
  refine ⟨queries_prgOfPRFReduction x A, run_prgOfPRFReduction x A, ?_⟩
  -- with the oracle `F k`, the reduction shows `A` the string `G k`
  have hreal : prgReal (prgOfPRF F x) A = PRF.prfReal F (prgOfPRFReduction x A) := by
    rw [prgReal, PRF.prfReal, hA, ← Cslib.Probability.PMF.uniformOfFintype_prod, PMF.map_bind]
    refine congrArg _ (funext fun k => ?_)
    rw [PMF.map_comp]
    exact congrArg (PMF.map · _) (funext fun r => (run_prgOfPRFReduction x A r (F k)).symm)
  -- with a random function, the answers at the distinct points are uniform
  have hrand : prgRand A = PRF.prfRand (prgOfPRFReduction x A) := by
    rw [prgRand, PRF.prfRand, hA, ← Cslib.Probability.PMF.uniformOfFintype_prod, PMF.map_bind,
      ← uniformOfFintype_map_eval (Y := Y) hx, PMF.bind_map]
    refine congrArg _ (funext fun f => ?_)
    rw [Function.comp_apply, PMF.map_comp]
    exact congrArg (PMF.map · _) (funext fun r => (run_prgOfPRFReduction x A r f).symm)
  rw [prgAdvantage, advantage, winProb, winProb, hreal, hrand, PRF.prfAdvantage]

end Reduction

/-! ### Asymptotic security -/

/-- **Asymptotic PRG security from a PRF.** Let $K_n$, $X_n$, $Y_n$ and $R_n$ be families of finite
sets with $K_n$, $Y_n$ and $R_n$ nonempty, let $F_n : K_n \to X_n \to Y_n$ be a family of keyed
functions, and for each $n$ let $x_{n,1}, \dots, x_{n,\ell(n)} \in X_n$ be distinct points with
$|K_n| < |Y_n|^{\ell(n)}$. Let $G_n(k) = (F_n(k, x_{n,1}), \dots, F_n(k, x_{n,\ell(n)}))$. Take a
class of admissible distinguisher families for $G$, with coins in $R_n$, each of which draws its
coins uniformly from $R_n$, and a class of admissible PRF distinguisher families for $F$, with coins
in $R_n$, that contains, for every admissible family $A$, the family of PRF distinguishers built
from $A_n$ (query $x_{n,1}, \dots, x_{n,\ell(n)}$ and output the guess of $A_n$ on the answers). If
$F$ is a secure PRF relative to that class, then $G$ is a secure PRG relative to the admissible
distinguisher families: it expands, and every admissible family has negligible PRG advantage.

This is the asymptotic form of Boneh and Shoup, Theorem 4.8. The condition
$|K_n| < |Y_n|^{\ell(n)}$ is used only for expansion. It comes from the asymptotic PRG security
`PRGSecure`, which requires expansion, following Katz and Lindell; Boneh and Shoup's
Theorem 4.8 has no such hypothesis, and their Definition 3.1 of a secure PRG does not require
expansion. The efficiency of $F$, of $G$ and of the distinguishers is not modelled; any
restriction on the distinguishers is what the two classes encode. -/
theorem prgSecure_prgOfPRF {K X Y R : ℕ → Type*} [∀ n, Fintype (K n)] [∀ n, Nonempty (K n)]
    [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)] [∀ n, Fintype (Y n)] [∀ n, Nonempty (Y n)]
    [∀ n, Fintype (R n)] [∀ n, Nonempty (R n)] (F : (n : ℕ) → K n → X n → Y n) {ℓ : ℕ → ℕ}
    {x : (n : ℕ) → Fin (ℓ n) → X n} (hx : ∀ n, Function.Injective (x n))
    (hexp : ∀ n, Fintype.card (K n) < Fintype.card (Y n) ^ ℓ n)
    (AdmA : ((n : ℕ) → Distinguisher (Fin (ℓ n) → Y n) (R n)) → Prop)
    (AdmB : ((n : ℕ) → R n → OracleComp (X n) (Y n) Bool) → Prop)
    (hcoins : ∀ A, AdmA A → ∀ n, (A n).coins = Cslib.Probability.PMF.uniformOfFintype (R n))
    (hred : ∀ A, AdmA A → AdmB fun n => prgOfPRFReduction (x n) (A n))
    (hF : PRF.PRFSecure F AdmB) :
    PRGSecure (fun n => prgOfPRF (F n) (x n)) R AdmA := by
  refine ⟨fun n => by simpa using hexp n, ?_⟩
  exact AsymptoticallySecure.of_reduction (fun A n => prgOfPRFReduction (x n) (A n)) hred
    negligibleAdv_zero (fun A hA n => by
      rw [(prgAdvantage_prgOfPRF_eq (F n) (hx n) (A n) (hcoins A hA n)).2.2, add_zero]) hF

end Cslib.Crypto.PRG
