/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Logic.Function.DependsOn
public import MathlibExt.Analysis.Fourier.BooleanCube
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.IntervalCases

/-!
# The Servedio–Tan–Verbin junta conjecture is false (O'Donnell, Problem 24)

R. O'Donnell, Open Problems in Analysis of Boolean Functions, Problem 24 (Servedio–Tan–Verbin
Conjecture, marked disproved in the list): fix any `ε > 0`. Then every monotone `f : {-1,1}ⁿ →
{-1,1}` is `ε`-close to a `poly(deg(f))`-junta. The main result of this file,
`servedioTanVerbinConjecture_refuted`, shows that this conjecture (`servedioTanVerbinConjecture`)
is false, following Kane's counterexample.

Source: R. O'Donnell, Open Problems in Analysis of Boolean Functions (2012), arXiv:1204.6447,
Problem 24 (Servedio–Tan–Verbin Conjecture). UnsolvedMath record UM-00800453 (`AMR-127-0022`),
dataset ulamai/UnsolvedMath v1.8.0.

Boolean functions are `f : {0,1}ⁿ → {0,1}` on `Fin n → Bool` with the coordinatewise order (`false <
true`), as in Kane's paper; the `{-1,1}` encoding of the source is the same up to relabeling and
does not change monotonicity, distances or degrees. `deg f` is MathlibExt's
`BooleanCube.booleanDegree` (total degree of the unique real multilinear extension, the Fourier
degree). A `poly(d)` bound is written `(d + 2) ^ C`: every polynomial is bounded by such a power for
`d ≥ 0` and conversely. `ε`-close means disagreeing on at most `ε 2ⁿ` inputs, and a `k`-junta is a
function of at most `k` coordinates: Mathlib's `DependsOn g J` with `|J| ≤ k`.

## Proof outline

The proof follows D. M. Kane, *A low-depth monotone function that is not an approximate junta*
(arXiv:1206.6541), with his random family of sets replaced by a deterministic choice.

* **The function.** There are `t * b` variables `x (ℓ, u)` (`ℓ < t`, `u < b`) and `m` variables
  `y j`. Each `j < m` has a selector `S j : Fin t → Fin b`, picking one `x`-variable in each of
  the `t` blocks. Let `T(x)` be the set of `j` such that `x (ℓ, S j ℓ)` is true for every `ℓ`.
  The function is true when `|T(x)| ≥ 2`, false when `T(x)` is empty, and equal to `y j` when
  `T(x) = {j}`. It is monotone, and it is computed by reading the `x`-variables and then at most
  one `y`-variable, so its Boolean degree is at most `t * b + 1`.
* **Distance to juntas.** Let `g` depend only on a set `J` of coordinates, and let `I` be the set
  of `j` with `y j ∈ J`. Flipping `y j` on an input with `T(x) = {j}` and `j ∉ I` changes the
  function but not `g`, so `f` and `g` differ on at least half of the inputs with `T(x) = {j}`
  for some `j ∉ I`.
* **Second moment.** The indicator of these inputs is at least `2|T| - |T|² - |T ∩ I|`. Over the
  cube, the averages of `|T|` and `|T ∩ I|` are `m 2⁻ᵗ` and `|I| 2⁻ᵗ ≤ |J| 2⁻ᵗ`, and the average
  of `|T|²` is `2⁻²ᵗ ∑_{i,j} 2^{a(i,j)}`, where `a(i,j)` counts the blocks in which `S i` and
  `S j` agree.
* **Choosing the selectors.** Averaging over a new selector `σ` gives
  `∑_σ 2^{a(σ,τ)} = (b + 1)ᵗ`, so the selectors can be chosen one at a time with
  `bᵗ ∑_{i,j} 2^{a(i,j)} ≤ m bᵗ 2ᵗ + m² (b + 1)ᵗ`. With `b = t`, `(t + 1)ᵗ ≤ 3 tᵗ`.
* **Parameters.** With `b = t` and `m = 2ᵗ⁻³`, the function has degree at most `t² + 1` and
  differs on at least `2ⁿ / 32` inputs from every function of at most `2ᵗ / 64` coordinates: a
  junta size `exp(Ω(√d))` in the degree `d`, as in Kane's theorem. Since `64 (t² + 3) ^ C ≤ 2ᵗ`
  for large `t`, no junta size `(deg f + 2) ^ C` works for `ε = 1 / 64`.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.MonotoneJuntaApproximationAMR127Problem0022Wanted

open BooleanCube Finset

/-- **The Servedio–Tan–Verbin conjecture.** Order $\{0,1\}^n$ coordinatewise with $0 < 1$, and
write $\deg f$ for the Boolean degree of a function $f : \{0,1\}^n \to \{0,1\}$. This is the
statement that for every real $\varepsilon > 0$ there is a natural number $C$ such that for every
$n \in \mathbb{N}$ and every monotone $f : \{0,1\}^n \to \{0,1\}$ there are a set $J$ of at most
$(\deg f + 2)^C$ coordinates and a function $g : \{0,1\}^n \to \{0,1\}$ that depends only on the
coordinates in $J$ such that $f(x) \ne g(x)$ for at most $\varepsilon 2^n$ points
$x \in \{0,1\}^n$.

The junta size $(\deg f + 2)^C$ expresses a polynomial bound in $\deg f$: every polynomial in
$d \ge 0$ is at most $(d + 2)^C$ for some $C$. -/
def servedioTanVerbinConjecture : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℕ, ∀ (n : ℕ) (f : (Fin n → Bool) → Bool), Monotone f →
    ∃ (J : Finset (Fin n)) (g : (Fin n → Bool) → Bool),
      J.card ≤ (BooleanCube.booleanDegree f + 2) ^ C ∧ DependsOn g (J : Set (Fin n)) ∧
        ((Finset.univ.filter fun x => f x ≠ g x).card : ℝ) ≤ ε * 2 ^ n

/-! ### Degree bound from a sum of products -/

/-- If the indicator of `f` is a sum of products `c a * ∏ i, g a i (x i)` in which, for each `a`,
all but at most `D` of the factors `g a i` are constant, then the Boolean degree of `f` is at most
`D`. -/
private theorem booleanDegree_le_of_eq_sum_prod {n : ℕ} {κ : Type*} (s : Finset κ)
    (c : κ → ℝ) (g : κ → Fin n → Bool → ℝ) (f : BoolCube n → Bool) (D : ℕ)
    (hf : ∀ x, (if f x then (1 : ℝ) else 0) = ∑ a ∈ s, c a * ∏ i, g a i (x i))
    (hD : ∀ a ∈ s, ∃ U : Finset (Fin n), U.card ≤ D ∧ ∀ i ∉ U, g a i true = g a i false) :
    booleanDegree f ≤ D := by
  classical
  have hME : multilinearExtension f = ∑ a ∈ s, MvPolynomial.C (c a) *
      ∏ i, (MvPolynomial.C (g a i true) * MvPolynomial.X i +
        MvPolynomial.C (g a i false) * (1 - MvPolynomial.X i)) := by
    rw [multilinearExtension]
    have hx : ∀ x : BoolCube n, MvPolynomial.C (if f x then (1 : ℝ) else 0) * cubeBasis x =
        ∑ a ∈ s, MvPolynomial.C (c a) * ∏ i, (MvPolynomial.C (g a i (x i)) *
          (if x i then MvPolynomial.X i else 1 - MvPolynomial.X i)) := by
      intro x
      rw [hf x, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_mul, map_prod, cubeBasis, mul_assoc, ← Finset.prod_mul_distrib]
    rw [Finset.sum_congr rfl fun x _ => hx x, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.mul_sum]
    congr 1
    have h := Finset.sum_prod_piFinset (R := MvPolynomial (Fin n) ℝ) (Finset.univ : Finset Bool)
      (fun i v => MvPolynomial.C (g a i v) *
        (if v then MvPolynomial.X i else 1 - MvPolynomial.X i))
    rw [Fintype.piFinset_univ] at h
    rw [h]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp
  rw [booleanDegree, hME]
  refine MvPolynomial.totalDegree_finsetSum_le fun a ha => ?_
  obtain ⟨U, hU, hconst⟩ := hD a ha
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  calc ∑ i, (MvPolynomial.C (g a i true) * MvPolynomial.X i +
        MvPolynomial.C (g a i false) * (1 - MvPolynomial.X i)).totalDegree
      ≤ ∑ i, if i ∈ U then 1 else 0 := by
        refine Finset.sum_le_sum fun i _ => ?_
        split_ifs with hi
        · refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
          · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
            rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
          · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
            rw [MvPolynomial.totalDegree_C, zero_add]
            refine (MvPolynomial.totalDegree_sub _ _).trans ?_
            rw [MvPolynomial.totalDegree_one, MvPolynomial.totalDegree_X]
            simp
        · rw [hconst i hi]
          have : MvPolynomial.C (g a i false) * MvPolynomial.X i +
              MvPolynomial.C (g a i false) * (1 - MvPolynomial.X i) =
                (MvPolynomial.C (g a i false) : MvPolynomial (Fin n) ℝ) := by
            ring
          rw [this, MvPolynomial.totalDegree_C]
    _ = U.card := by simp
    _ ≤ D := hU

/-- The points of the cube that are true on a set `A` of coordinates are a `2 ^ (-|A|)`
fraction of the cube. -/
private theorem card_filter_forall_true_mul {n : ℕ} (A : Finset (Fin n)) :
    (univ.filter fun z : Fin n → Bool => ∀ i ∈ A, z i = true).card * 2 ^ A.card = 2 ^ n := by
  classical
  have h : (univ.filter fun z : Fin n → Bool => ∀ i ∈ A, z i = true) =
      Fintype.piFinset fun i => if i ∈ A then {true} else univ := by
    ext z
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro hz i
      split_ifs with hi
      · simp [hz i hi]
      · simp
    · intro hz i hi
      simpa [hi] using hz i
  rw [h, Fintype.card_piFinset]
  have h2 : ∀ i, (if i ∈ A then ({true} : Finset Bool) else univ).card =
      if i ∈ A then 1 else 2 := by
    intro i
    split_ifs <;> simp
  simp_rw [h2]
  rw [Finset.prod_ite, prod_const_one, one_mul, prod_const, ← pow_add]
  congr 1
  rw [show (univ.filter fun x => x ∉ A) = Aᶜ by ext; simp, card_compl, Fintype.card_fin]
  have := Finset.card_le_univ A
  rw [Fintype.card_fin] at this
  omega

/-! ### Selectors and their agreements -/

/-- The number of blocks in which two selectors agree. -/
private def agree {t b : ℕ} (σ τ : Fin t → Fin b) : ℕ :=
  (univ.filter fun ℓ => σ ℓ = τ ℓ).card

private theorem agree_comm {t b : ℕ} (σ τ : Fin t → Fin b) : agree σ τ = agree τ σ := by
  simp only [agree, eq_comm]

private theorem agree_self {t b : ℕ} (σ : Fin t → Fin b) : agree σ σ = t := by
  simp [agree]

/-- Summing `2 ^ agree σ τ` over all selectors `σ` gives `(b + 1) ^ t`. -/
private theorem sum_two_pow_agree {t b : ℕ} (τ : Fin t → Fin b) :
    ∑ σ : Fin t → Fin b, 2 ^ agree σ τ = (b + 1) ^ t := by
  classical
  have h1 : ∀ σ : Fin t → Fin b, 2 ^ agree σ τ = ∏ ℓ, (if σ ℓ = τ ℓ then 2 else 1) := by
    intro σ
    rw [agree, Finset.prod_ite, prod_const, prod_const_one, mul_one]
  simp_rw [h1]
  have h := Finset.sum_prod_piFinset (R := ℕ) (univ : Finset (Fin b))
    (fun ℓ u => if u = τ ℓ then 2 else 1)
  rw [Fintype.piFinset_univ] at h
  rw [h]
  have h2 : ∀ ℓ, ∑ u : Fin b, (if u = τ ℓ then 2 else 1) = b + 1 := by
    intro ℓ
    have : ∀ u : Fin b, (if u = τ ℓ then 2 else 1) = 1 + if u = τ ℓ then 1 else 0 := by
      intro u
      split_ifs <;> rfl
    simp_rw [this]
    rw [sum_add_distrib]
    simp
  simp [h2]

/-- The sum of `2 ^ agree (S i) (S j)` over all ordered pairs of selectors in a family. -/
private def pairSum {t b m : ℕ} (S : Fin m → Fin t → Fin b) : ℕ :=
  ∑ i, ∑ j, 2 ^ agree (S i) (S j)

/-- Choosing the selectors one at a time, each at most average, keeps `pairSum` small. -/
private theorem exists_selectors (t b : ℕ) (hb : 0 < b) : ∀ m : ℕ,
    ∃ S : Fin m → Fin t → Fin b, b ^ t * pairSum S ≤ m * b ^ t * 2 ^ t + m ^ 2 * (b + 1) ^ t
  | 0 => ⟨Fin.elim0, by simp [pairSum]⟩
  | m + 1 => by
    obtain ⟨S, hS⟩ := exists_selectors t b hb m
    have hne : (univ : Finset (Fin t → Fin b)).Nonempty := by
      have : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩
      exact univ_nonempty
    obtain ⟨σ, -, hσ⟩ : ∃ σ ∈ (univ : Finset (Fin t → Fin b)),
        b ^ t * ∑ j, 2 ^ agree σ (S j) ≤ m * (b + 1) ^ t := by
      apply Finset.exists_le_of_sum_le hne
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp_rw [sum_two_pow_agree]
      simp [Finset.card_univ]
    refine ⟨Fin.cons σ S, ?_⟩
    have hsplit : pairSum (Fin.cons σ S : Fin (m + 1) → Fin t → Fin b) =
        2 ^ t + 2 * ∑ j, 2 ^ agree σ (S j) + pairSum S := by
      simp only [pairSum, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, agree_self]
      rw [Finset.sum_add_distrib]
      rw [show ∑ i, 2 ^ agree (S i) σ = ∑ j, 2 ^ agree σ (S j) from by simp [agree_comm]]
      ring
    rw [hsplit]
    calc b ^ t * (2 ^ t + 2 * ∑ j, 2 ^ agree σ (S j) + pairSum S)
        = b ^ t * 2 ^ t + 2 * (b ^ t * ∑ j, 2 ^ agree σ (S j)) + b ^ t * pairSum S := by ring
      _ ≤ b ^ t * 2 ^ t + 2 * (m * (b + 1) ^ t) + (m * b ^ t * 2 ^ t + m ^ 2 * (b + 1) ^ t) := by
        gcongr
      _ ≤ (m + 1) * b ^ t * 2 ^ t + (m + 1) ^ 2 * (b + 1) ^ t := by
        rw [show (m + 1) * b ^ t * 2 ^ t + (m + 1) ^ 2 * (b + 1) ^ t =
          (b ^ t * 2 ^ t + 2 * (m * (b + 1) ^ t) + (m * b ^ t * 2 ^ t + m ^ 2 * (b + 1) ^ t)) +
            (b + 1) ^ t by ring]
        exact Nat.le_add_right _ _

/-! ### The construction -/

variable {t b m n : ℕ}

/-- The selectors `j` whose chosen variables `α (ℓ, S j ℓ)` are all true, for an assignment `α`
of the `x`-variables. -/
private def kaneSetX (S : Fin m → Fin t → Fin b) (α : Fin t × Fin b → Bool) : Finset (Fin m) :=
  univ.filter fun j => ∀ ℓ, α (ℓ, S j ℓ) = true

/-- The set `T(z)` of selectors whose chosen `x`-variables are all true at the point `z`; the
coordinates of the cube are the `x`-variables `e (inl (ℓ, u))` and the `y`-variables
`e (inr j)`. -/
private def kaneSet (e : (Fin t × Fin b) ⊕ Fin m ≃ Fin n) (S : Fin m → Fin t → Fin b)
    (z : Fin n → Bool) : Finset (Fin m) :=
  kaneSetX S fun p => z (e (Sum.inl p))

/-- Kane's function: true if `|T(z)| ≥ 2`, false if `T(z)` is empty, and `y j` if
`T(z) = {j}`. -/
private def kaneFun (e : (Fin t × Fin b) ⊕ Fin m ≃ Fin n) (S : Fin m → Fin t → Fin b)
    (z : Fin n → Bool) : Bool :=
  decide (2 ≤ (kaneSet e S z).card ∨ ∃ j ∈ kaneSet e S z, z (e (Sum.inr j)) = true)

private theorem kaneSet_mono (e : (Fin t × Fin b) ⊕ Fin m ≃ Fin n) (S : Fin m → Fin t → Fin b)
    {z z' : Fin n → Bool} (h : z ≤ z') : kaneSet e S z ⊆ kaneSet e S z' := by
  intro j hj
  simp only [kaneSet, kaneSetX, mem_filter, mem_univ, true_and] at hj ⊢
  intro ℓ
  have h1 := h (e (Sum.inl (ℓ, S j ℓ)))
  rw [hj ℓ] at h1
  exact Bool.le_iff_imp.mp h1 rfl

private theorem kaneFun_monotone (e : (Fin t × Fin b) ⊕ Fin m ≃ Fin n)
    (S : Fin m → Fin t → Fin b) : Monotone (kaneFun e S) := by
  intro z z' h
  have hT := kaneSet_mono e S h
  rw [Bool.le_iff_imp]
  simp only [kaneFun, decide_eq_true_eq]
  rintro (h2 | ⟨j, hj, hy⟩)
  · exact Or.inl (h2.trans (card_le_card hT))
  · refine Or.inr ⟨j, hT hj, ?_⟩
    have h1 := h (e (Sum.inr j))
    rw [hy] at h1
    exact Bool.le_iff_imp.mp h1 rfl

private theorem kaneFun_indicator (e : (Fin t × Fin b) ⊕ Fin m ≃ Fin n)
    (S : Fin m → Fin t → Fin b) (x : Fin n → Bool) :
    (if kaneFun e S x then (1 : ℝ) else 0) =
      (if 2 ≤ (kaneSet e S x).card then 1 else 0) +
        ∑ j, (if kaneSet e S x = {j} then 1 else 0) * (if x (e (Sum.inr j)) then 1 else 0) := by
  classical
  by_cases h2 : 2 ≤ (kaneSet e S x).card
  · have hf : kaneFun e S x = true := by simp [kaneFun, h2]
    have hz : ∀ j, kaneSet e S x ≠ {j} := by
      intro j hj
      rw [hj, card_singleton] at h2
      omega
    simp [hf, h2, hz]
  · rcases Nat.lt_or_ge (kaneSet e S x).card 1 with h0 | h1
    · have hT : kaneSet e S x = ∅ := card_eq_zero.mp (by omega)
      have hf : kaneFun e S x = false := by simp [kaneFun, hT]
      simp [hf, hT, eq_comm (a := (∅ : Finset (Fin m)))]
    · obtain ⟨j0, hj0⟩ := card_eq_one.mp (le_antisymm (by omega) h1)
      have hf : kaneFun e S x = x (e (Sum.inr j0)) := by simp [kaneFun, hj0]
      simp only [hf, hj0, card_singleton, singleton_inj]
      rw [Finset.sum_eq_single j0 (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
      simp

/-- Kane's function reads the `t * b` variables `x` and then at most one variable `y`, so its
Boolean degree is at most `t * b + 1`. -/
private theorem booleanDegree_kaneFun (e : (Fin t × Fin b) ⊕ Fin m ≃ Fin n)
    (S : Fin m → Fin t → Fin b) : booleanDegree (kaneFun e S) ≤ t * b + 1 := by
  classical
  refine booleanDegree_le_of_eq_sum_prod (κ := (Fin t × Fin b → Bool) × Option (Fin m)) univ
    (fun a => Option.elim a.2 (if 2 ≤ (kaneSetX S a.1).card then 1 else 0)
      (fun j => if kaneSetX S a.1 = {j} then 1 else 0))
    (fun a i v => Sum.elim (fun p => if v = a.1 p then 1 else 0)
      (fun j => if a.2 = some j then (if v then 1 else 0) else 1) (e.symm i))
    (kaneFun e S) (t * b + 1) ?_ ?_
  · intro x
    have hprod : ∀ a : (Fin t × Fin b → Bool) × Option (Fin m),
        (∏ i, Sum.elim (fun p => if x i = a.1 p then (1 : ℝ) else 0)
          (fun j => if a.2 = some j then (if x i then 1 else 0) else 1) (e.symm i)) =
        (if a.1 = (fun p => x (e (Sum.inl p))) then 1 else 0) *
          Option.elim a.2 1 (fun j => if x (e (Sum.inr j)) then 1 else 0) := by
      intro a
      rw [← e.prod_comp]
      simp only [Equiv.symm_apply_apply, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
      congr 1
      · rw [Finset.prod_boole]
        simp [funext_iff, eq_comm]
      · rcases a with ⟨α, _ | j⟩
        · simp
        · simp [Finset.prod_ite_eq]
    simp_rw [hprod]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single (fun p => x (e (Sum.inl p))) (fun α _ hα => by simp [hα])
      (by simp)]
    simp only [ite_true, one_mul, Fintype.sum_option, Option.elim, mul_one]
    rw [kaneFun_indicator]
    rfl
  · rintro ⟨α, o⟩ -
    have himg : (univ.image fun p : Fin t × Fin b => e (Sum.inl p)).card ≤ t * b :=
      card_image_le.trans (by simp)
    refine ⟨Option.elim o (univ.image fun p => e (Sum.inl p))
      (fun j => insert (e (Sum.inr j)) (univ.image fun p => e (Sum.inl p))), ?_, ?_⟩
    · cases o with
      | none => exact himg.trans (Nat.le_succ _)
      | some j => exact (card_insert_le _ _).trans (Nat.succ_le_succ himg)
    · intro i hi
      obtain ⟨k, rfl⟩ := e.surjective i
      rcases k with p | j'
      · exfalso
        apply hi
        cases o <;> simp
      · simp only [Equiv.symm_apply_apply, Sum.elim_inr]
        cases o with
        | none => simp
        | some j =>
          by_cases hjj : j = j'
          · subst hjj
            exfalso
            apply hi
            simp
          · simp [hjj]

/-! ### Counting -/

/-- The `x`-variables read by the selector `j`. -/
private def kaneSupport (e : (Fin t × Fin b) ⊕ Fin m ≃ Fin n) (S : Fin m → Fin t → Fin b)
    (j : Fin m) : Finset (Fin n) :=
  univ.image fun ℓ => e (Sum.inl (ℓ, S j ℓ))

private theorem mem_kaneSet_iff (e : (Fin t × Fin b) ⊕ Fin m ≃ Fin n)
    (S : Fin m → Fin t → Fin b) (z : Fin n → Bool) (j : Fin m) :
    j ∈ kaneSet e S z ↔ ∀ k ∈ kaneSupport e S j, z k = true := by
  simp [kaneSet, kaneSetX, kaneSupport]

private theorem kaneSupport_injective (e : (Fin t × Fin b) ⊕ Fin m ≃ Fin n)
    (S : Fin m → Fin t → Fin b) (j : Fin m) :
    Function.Injective fun ℓ => e (Sum.inl (ℓ, S j ℓ)) := by
  intro ℓ ℓ' h
  have := e.injective h
  simp only [Sum.inl.injEq, Prod.mk.injEq] at this
  exact this.1

private theorem card_kaneSupport (e : (Fin t × Fin b) ⊕ Fin m ≃ Fin n)
    (S : Fin m → Fin t → Fin b) (j : Fin m) : (kaneSupport e S j).card = t := by
  rw [kaneSupport, card_image_of_injective _ (kaneSupport_injective e S j)]
  simp

private theorem card_kaneSupport_inter (e : (Fin t × Fin b) ⊕ Fin m ≃ Fin n)
    (S : Fin m → Fin t → Fin b) (i j : Fin m) :
    (kaneSupport e S i ∩ kaneSupport e S j).card = agree (S i) (S j) := by
  classical
  have h : kaneSupport e S i ∩ kaneSupport e S j =
      (univ.filter fun ℓ => S i ℓ = S j ℓ).image fun ℓ => e (Sum.inl (ℓ, S i ℓ)) := by
    ext k
    simp only [kaneSupport, mem_inter, mem_image, mem_univ, true_and, mem_filter]
    constructor
    · rintro ⟨⟨ℓ, rfl⟩, ⟨ℓ', h⟩⟩
      have := e.injective h
      simp only [Sum.inl.injEq, Prod.mk.injEq] at this
      obtain ⟨rfl, h2⟩ := this
      exact ⟨ℓ', h2.symm, rfl⟩
    · rintro ⟨ℓ, hℓ, rfl⟩
      exact ⟨⟨ℓ, rfl⟩, ⟨ℓ, by rw [hℓ]⟩⟩
  rw [h, card_image_of_injective _ (kaneSupport_injective e S i)]
  rfl

/-- Each selector is active on a `2 ^ (-t)` fraction of the cube. -/
private theorem card_mem_kaneSet_mul (e : (Fin t × Fin b) ⊕ Fin m ≃ Fin n)
    (S : Fin m → Fin t → Fin b) (j : Fin m) :
    (univ.filter fun z : Fin n → Bool => j ∈ kaneSet e S z).card * 2 ^ t = 2 ^ n := by
  classical
  have h := card_filter_forall_true_mul (kaneSupport e S j)
  rw [card_kaneSupport] at h
  rw [← h, filter_congr fun z _ => mem_kaneSet_iff e S z j]

/-- Two selectors are both active on a `2 ^ (agree - 2t)` fraction of the cube. -/
private theorem card_mem_kaneSet_pair_mul (e : (Fin t × Fin b) ⊕ Fin m ≃ Fin n)
    (S : Fin m → Fin t → Fin b) (i j : Fin m) :
    (univ.filter fun z : Fin n → Bool => i ∈ kaneSet e S z ∧ j ∈ kaneSet e S z).card *
      (2 ^ t * 2 ^ t) = 2 ^ n * 2 ^ agree (S i) (S j) := by
  classical
  have h := card_filter_forall_true_mul (kaneSupport e S i ∪ kaneSupport e S j)
  have hu := card_union_add_card_inter (kaneSupport e S i) (kaneSupport e S j)
  rw [card_kaneSupport, card_kaneSupport, card_kaneSupport_inter] at hu
  have hf : (univ.filter fun z : Fin n → Bool => i ∈ kaneSet e S z ∧ j ∈ kaneSet e S z) =
      univ.filter fun z => ∀ k ∈ kaneSupport e S i ∪ kaneSupport e S j, z k = true := by
    apply filter_congr
    intro z _
    simp only [mem_kaneSet_iff, mem_union]
    constructor
    · rintro ⟨h1, h2⟩ k (hk | hk)
      · exact h1 k hk
      · exact h2 k hk
    · intro h
      exact ⟨fun k hk => h k (Or.inl hk), fun k hk => h k (Or.inr hk)⟩
  rw [hf, ← pow_add, ← hu, pow_add, ← mul_assoc, h]

/-! ### Pairing inputs that differ in one `y`-variable -/

/-- Flip the `y`-variables of the selectors in `T(z)`. -/
private def kaneFlip (e : (Fin t × Fin b) ⊕ Fin m ≃ Fin n) (S : Fin m → Fin t → Fin b)
    (z : Fin n → Bool) (i : Fin n) : Bool :=
  if ∃ j ∈ kaneSet e S z, e (Sum.inr j) = i then !z i else z i

private theorem kaneSet_kaneFlip (e : (Fin t × Fin b) ⊕ Fin m ≃ Fin n)
    (S : Fin m → Fin t → Fin b) (z : Fin n → Bool) :
    kaneSet e S (kaneFlip e S z) = kaneSet e S z := by
  have : (fun p => kaneFlip e S z (e (Sum.inl p))) = fun p => z (e (Sum.inl p)) := by
    funext p
    rw [kaneFlip, ite_eq_right]
    rintro ⟨j, -, hj⟩
    exact Sum.inr_ne_inl (e.injective hj)
  rw [kaneSet, this]
  rfl

private theorem kaneFlip_kaneFlip (e : (Fin t × Fin b) ⊕ Fin m ≃ Fin n)
    (S : Fin m → Fin t → Fin b) (z : Fin n → Bool) :
    kaneFlip e S (kaneFlip e S z) = z := by
  funext i
  have h1 : kaneFlip e S (kaneFlip e S z) i =
      if ∃ j ∈ kaneSet e S z, e (Sum.inr j) = i then !(kaneFlip e S z i)
        else kaneFlip e S z i := by
    rw [← kaneSet_kaneFlip e S z]
    rfl
  rw [h1]
  by_cases hc : ∃ j ∈ kaneSet e S z, e (Sum.inr j) = i
  · rw [ite_eq_left hc, kaneFlip, ite_eq_left hc, Bool.not_not]
  · rw [ite_eq_right hc, kaneFlip, ite_eq_right hc]

/-- A function `g` of the coordinates in `J` differs from Kane's function on at least half of
the points `z` with `T(z) = {j}` for a selector `j` whose variable `y j` is not in `J`. -/
private theorem card_kaneA_le (e : (Fin t × Fin b) ⊕ Fin m ≃ Fin n)
    (S : Fin m → Fin t → Fin b) (J : Finset (Fin n)) (g : (Fin n → Bool) → Bool)
    (hg : DependsOn g (J : Set (Fin n))) :
    (univ.filter fun z => ∃ j, e (Sum.inr j) ∉ J ∧ kaneSet e S z = {j}).card ≤
      2 * (univ.filter fun z => kaneFun e S z ≠ g z).card := by
  classical
  set A := univ.filter fun z : Fin n → Bool => ∃ j, e (Sum.inr j) ∉ J ∧ kaneSet e S z = {j}
    with hA
  set B := univ.filter fun z : Fin n → Bool => kaneFun e S z ≠ g z with hB
  have key : ∀ z ∈ A, kaneFlip e S z ∈ A ∧ (kaneFlip e S z ∈ B ↔ z ∉ B) := by
    intro z hz
    simp only [hA, mem_filter, mem_univ, true_and] at hz
    obtain ⟨j, hjJ, hT⟩ := hz
    have hT' : kaneSet e S (kaneFlip e S z) = {j} := by rw [kaneSet_kaneFlip, hT]
    refine ⟨by simp only [hA, mem_filter, mem_univ, true_and]; exact ⟨j, hjJ, hT'⟩, ?_⟩
    have hf1 : kaneFun e S z = z (e (Sum.inr j)) := by simp [kaneFun, hT]
    have hf2 : kaneFun e S (kaneFlip e S z) = !z (e (Sum.inr j)) := by
      simp [kaneFun, hT', kaneFlip, hT]
    have hg2 : g (kaneFlip e S z) = g z := by
      apply hg
      intro i hi
      rw [kaneFlip, ite_eq_right]
      rintro ⟨j', hj', rfl⟩
      rw [hT, mem_singleton] at hj'
      subst hj'
      exact hjJ hi
    simp only [hB, mem_filter, mem_univ, true_and, hf1, hf2, hg2]
    cases z (e (Sum.inr j)) <;> cases g z <;> simp
  have hcard : (A.filter fun z => z ∈ B).card = (A.filter fun z => z ∉ B).card := by
    apply Finset.card_nbij' (kaneFlip e S) (kaneFlip e S)
    · intro z hz
      simp only [coe_filter, Set.mem_ofPred_eq] at hz ⊢
      exact ⟨(key z hz.1).1, fun h => ((key z hz.1).2.mp h) hz.2⟩
    · intro z hz
      simp only [coe_filter, Set.mem_ofPred_eq] at hz ⊢
      exact ⟨(key z hz.1).1, (key z hz.1).2.mpr hz.2⟩
    · intro z _
      exact kaneFlip_kaneFlip e S z
    · intro z _
      exact kaneFlip_kaneFlip e S z
  have hsplit := Finset.card_filter_add_card_filter_not (s := A) (fun z => z ∈ B)
  have hsub : (A.filter fun z => z ∈ B).card ≤ B.card :=
    card_le_card fun z hz => (mem_filter.mp hz).2
  omega

/-! ### The second-moment bound -/

/-- The counting inequality behind Kane's theorem: for a function `g` of the coordinates in
`J`, with `D = pairSum S`,
`2ⁿ (2 m 2ᵗ - D - |J| 2ᵗ) ≤ 2ᵗ 2ᵗ (2 |{z | f z ≠ g z}|)`. -/
private theorem kane_count (e : (Fin t × Fin b) ⊕ Fin m ≃ Fin n) (S : Fin m → Fin t → Fin b)
    (J : Finset (Fin n)) (g : (Fin n → Bool) → Bool) (hg : DependsOn g (J : Set (Fin n))) :
    (2 : ℝ) ^ n * (2 * m * 2 ^ t - pairSum S - J.card * 2 ^ t) ≤
      2 ^ t * 2 ^ t * (2 * (univ.filter fun z => kaneFun e S z ≠ g z).card) := by
  classical
  set I : Finset (Fin m) := univ.filter fun j => e (Sum.inr j) ∈ J with hI
  have hIJ : I.card ≤ J.card := by
    apply Finset.card_le_card_of_injOn (fun j => e (Sum.inr j))
    · intro j hj
      simpa [hI] using hj
    · intro j _ j' _ h
      simpa using e.injective h
  have hA := card_kaneA_le e S J g hg
  -- the pointwise second-moment inequality
  have hpt : ∀ z : Fin n → Bool,
      2 * ((kaneSet e S z).card : ℝ) - ((kaneSet e S z).card : ℝ) ^ 2 -
          ((kaneSet e S z ∩ I).card : ℝ) ≤
        if (∃ j, e (Sum.inr j) ∉ J ∧ kaneSet e S z = {j}) then 1 else 0 := by
    intro z
    have hI0 : (0 : ℝ) ≤ ((kaneSet e S z ∩ I).card : ℝ) := Nat.cast_nonneg _
    have hif : (0 : ℝ) ≤ if (∃ j, e (Sum.inr j) ∉ J ∧ kaneSet e S z = {j}) then 1 else 0 := by
      split_ifs <;> norm_num
    rcases Nat.lt_or_ge (kaneSet e S z).card 2 with hlt | hge
    · rcases Nat.lt_or_ge (kaneSet e S z).card 1 with h0 | h1
      · have h0' : (kaneSet e S z).card = 0 := by omega
        rw [h0']
        push_cast
        linarith
      · obtain ⟨j, hj⟩ := card_eq_one.mp (le_antisymm (by omega) h1)
        by_cases hjJ : e (Sum.inr j) ∈ J
        · have hcap : (kaneSet e S z ∩ I).card = 1 := by
            rw [hj, card_eq_one]
            exact ⟨j, by ext k; simp [hI, hjJ]⟩
          rw [hcap, hj, card_singleton]
          push_cast
          split_ifs <;> norm_num
        · have hz : ∃ j, e (Sum.inr j) ∉ J ∧ kaneSet e S z = {j} := ⟨j, hjJ, hj⟩
          rw [ite_eq_left hz, hj, card_singleton]
          push_cast
          linarith
    · have hk : (2 : ℝ) ≤ ((kaneSet e S z).card : ℝ) := by exact_mod_cast hge
      nlinarith
  have hsum : ∑ z : Fin n → Bool, (2 * ((kaneSet e S z).card : ℝ) -
      ((kaneSet e S z).card : ℝ) ^ 2 - ((kaneSet e S z ∩ I).card : ℝ)) ≤
        ((univ.filter fun z => ∃ j, e (Sum.inr j) ∉ J ∧ kaneSet e S z = {j}).card : ℝ) := by
    rw [Finset.natCast_card_filter]
    exact Finset.sum_le_sum fun z _ => hpt z
  -- the moments
  have hcard : ∀ z : Fin n → Bool,
      (kaneSet e S z).card = ∑ j, if j ∈ kaneSet e S z then 1 else 0 := by
    intro z
    rw [Finset.sum_boole]
    simp
  have hS1 : 2 ^ t * ∑ z : Fin n → Bool, (kaneSet e S z).card = m * 2 ^ n := by
    simp_rw [hcard]
    rw [Finset.sum_comm, Finset.mul_sum]
    simp_rw [Finset.sum_boole, mul_comm (2 ^ t), Nat.cast_id, card_mem_kaneSet_mul]
    simp
  have hS2 : 2 ^ t * 2 ^ t * ∑ z : Fin n → Bool, (kaneSet e S z).card ^ 2 =
      2 ^ n * pairSum S := by
    have hsq : ∀ z : Fin n → Bool, (kaneSet e S z).card ^ 2 =
        ∑ i, ∑ j, if i ∈ kaneSet e S z ∧ j ∈ kaneSet e S z then 1 else 0 := by
      intro z
      rw [sq, hcard z, Finset.sum_mul_sum]
      simp_rw [ite_zero_mul_ite_zero, mul_one]
    simp_rw [hsq]
    rw [Finset.sum_comm]
    simp_rw [fun i => Finset.sum_comm (s := (univ : Finset (Fin n → Bool)))
      (t := (univ : Finset (Fin m)))
      (f := fun z j => if i ∈ kaneSet e S z ∧ j ∈ kaneSet e S z then 1 else 0)]
    simp_rw [Finset.sum_boole, Nat.cast_id, Finset.mul_sum, mul_comm (2 ^ t * 2 ^ t),
      card_mem_kaneSet_pair_mul]
    rw [pairSum, Finset.mul_sum]
    simp_rw [Finset.mul_sum]
  have hS3 : 2 ^ t * ∑ z : Fin n → Bool, (kaneSet e S z ∩ I).card = I.card * 2 ^ n := by
    have hcap : ∀ z : Fin n → Bool,
        (kaneSet e S z ∩ I).card = ∑ j ∈ I, if j ∈ kaneSet e S z then 1 else 0 := by
      intro z
      rw [Finset.sum_boole, Finset.filter_mem_eq_inter, inter_comm]
      rfl
    simp_rw [hcap]
    rw [Finset.sum_comm, Finset.mul_sum]
    simp_rw [Finset.sum_boole, mul_comm (2 ^ t), Nat.cast_id, card_mem_kaneSet_mul]
    simp
  -- combine in `ℝ`
  have hS1' : (2 : ℝ) ^ t * ∑ z : Fin n → Bool, ((kaneSet e S z).card : ℝ) = m * 2 ^ n := by
    exact_mod_cast hS1
  have hS2' : (2 : ℝ) ^ t * 2 ^ t * ∑ z : Fin n → Bool, ((kaneSet e S z).card : ℝ) ^ 2 =
      2 ^ n * pairSum S := by
    exact_mod_cast hS2
  have hS3' : (2 : ℝ) ^ t * ∑ z : Fin n → Bool, ((kaneSet e S z ∩ I).card : ℝ) =
      I.card * 2 ^ n := by
    exact_mod_cast hS3
  have hA' : ((univ.filter fun z => ∃ j, e (Sum.inr j) ∉ J ∧ kaneSet e S z = {j}).card : ℝ) ≤
      2 * (univ.filter fun z => kaneFun e S z ≠ g z).card := by
    exact_mod_cast hA
  have hIJ' : (I.card : ℝ) ≤ J.card := by exact_mod_cast hIJ
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  set s1 := ∑ z : Fin n → Bool, ((kaneSet e S z).card : ℝ)
  set s2 := ∑ z : Fin n → Bool, ((kaneSet e S z).card : ℝ) ^ 2
  set s3 := ∑ z : Fin n → Bool, ((kaneSet e S z ∩ I).card : ℝ)
  have hW : (0 : ℝ) ≤ 2 ^ t := by positivity
  have hP : (0 : ℝ) ≤ 2 ^ n := by positivity
  have h1 : (2 : ℝ) ^ t * 2 ^ t * (2 * s1 - s2 - s3) ≤
      2 ^ t * 2 ^ t * (2 * (univ.filter fun z => kaneFun e S z ≠ g z).card) :=
    mul_le_mul_of_nonneg_left (hsum.trans hA') (by positivity)
  have h2 : (2 : ℝ) ^ t * (I.card * 2 ^ n) ≤ 2 ^ t * (J.card * 2 ^ n) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hIJ' hP) hW
  have e1 : (2 : ℝ) ^ t * 2 ^ t * (2 * s1 - s2 - s3) =
      2 * 2 ^ t * (2 ^ t * s1) - 2 ^ t * 2 ^ t * s2 - 2 ^ t * (2 ^ t * s3) := by ring
  rw [e1, hS1', hS2', hS3'] at h1
  nlinarith

/-! ### Choice of the parameters -/

/-- `(t + 1) ^ t ≤ 3 t ^ t` for `t > 0`, since `(1 + 1 / t) ^ t ≤ e < 3`. -/
private theorem succ_pow_le_three_mul (t : ℕ) (ht : 0 < t) :
    ((t : ℝ) + 1) ^ t ≤ 3 * (t : ℝ) ^ t := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have h1 : (t : ℝ) + 1 = t * (1 + 1 / t) := by field_simp
  rw [h1, mul_pow]
  have h2 : (1 + 1 / (t : ℝ)) ^ t ≤ Real.exp 1 := by
    calc (1 + 1 / (t : ℝ)) ^ t ≤ (Real.exp (1 / t)) ^ t := by
          gcongr
          linarith [Real.add_one_le_exp (1 / (t : ℝ))]
      _ = Real.exp 1 := by
          rw [← Real.exp_nat_mul]
          congr 1
          field_simp
  have h3 : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have h4 : (0 : ℝ) ≤ (t : ℝ) ^ t := by positivity
  nlinarith

/-- Exponentials beat polynomials: `64 (t² + 3) ^ C ≤ 2 ^ t` for some `t ≥ 3`. -/
private theorem exists_large_t (C : ℕ) : ∃ t : ℕ, 3 ≤ t ∧ 64 * (t * t + 3) ^ C ≤ 2 ^ t := by
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt (2 * C) (one_lt_two : (1 : ℝ) < 2)
  have hpos : (0 : ℝ) < 1 / (64 * 4 ^ C) := by positivity
  have hev := hlim.eventually (gt_mem_nhds hpos)
  obtain ⟨t, ht, ht3⟩ := (hev.and (Filter.eventually_ge_atTop 3)).exists
  refine ⟨t, ht3, ?_⟩
  have htR : (3 : ℝ) ≤ t := by exact_mod_cast ht3
  have h1 : (t : ℝ) ^ (2 * C) * (64 * 4 ^ C) < 2 ^ t := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity), one_mul] at ht
    exact ht
  have h2 : (t : ℝ) * t + 3 ≤ 4 * (t : ℝ) ^ 2 := by nlinarith
  have h3 : ((t : ℝ) * t + 3) ^ C ≤ (4 * (t : ℝ) ^ 2) ^ C := by
    gcongr
  have h4 : (4 * (t : ℝ) ^ 2) ^ C = 4 ^ C * (t : ℝ) ^ (2 * C) := by
    rw [mul_pow, ← pow_mul]
  have h5 : (64 : ℝ) * ((t : ℝ) * t + 3) ^ C ≤ 2 ^ t := by
    rw [h4] at h3
    nlinarith
  exact_mod_cast h5

/-- **The Servedio–Tan–Verbin conjecture is false.** Order $\{0,1\}^n$ coordinatewise with
$0 < 1$, and write $\deg f$ for the Boolean degree of a function $f : \{0,1\}^n \to \{0,1\}$. It
is not the case that for every real $\varepsilon > 0$ there is a natural number $C$ such that for
every $n \in \mathbb{N}$ and every monotone $f : \{0,1\}^n \to \{0,1\}$ there are a set $J$ of at
most $(\deg f + 2)^C$ coordinates and a function $g : \{0,1\}^n \to \{0,1\}$ that depends only on
the coordinates in $J$ such that $f(x) \ne g(x)$ for at most $\varepsilon 2^n$ points
$x \in \{0,1\}^n$.

Kane constructed, for a fixed $\varepsilon > 0$, a constant $c > 0$ and every $d$, monotone
functions of decision-tree depth $d$ (hence degree at most $d$) that are $\varepsilon$-far from
every junta on $\exp(c \sqrt{d})$ coordinates; since $\exp(c \sqrt{d})$ eventually exceeds
$(d + 2)^C$, no polynomial junta size works for $\varepsilon / 2$. O'Donnell's list records the
conjecture as resolved in the negative by Kane.

Source: R.
O'Donnell, Open Problems in Analysis of Boolean Functions (2012), arXiv:1204.6447, Problem 24
(Servedio–Tan–Verbin Conjecture); resolution: D. M. Kane, A low-depth monotone function that is not
an approximate junta, arXiv:1206.6541 (2012); recorded as "RESOLVED (in the negative) by Daniel
Kane, 2012" in O'Donnell's list, Problem 24, Kane, Theorem 2: there is a constant ε > 0 such that
for every d there are k = exp(Ω(√d)) and a monotone f : {0,1}ⁿ → {0,1} computed by a depth-d
decision tree (so deg f ≤ d) that disagrees with every k-junta on at least an ε-fraction of inputs,
https://arxiv.org/abs/1206.6541.
-/
public theorem servedioTanVerbinConjecture_refuted : ¬ servedioTanVerbinConjecture := by
  intro H
  obtain ⟨C, hC⟩ := H (1 / 64) (by norm_num)
  obtain ⟨t, ht3, htC⟩ := exists_large_t C
  have ht0 : 0 < t := by omega
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = 2 ^ (t - 3) := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ := exists_selectors t t ht0 m
  let e := Fintype.equivFin ((Fin t × Fin t) ⊕ Fin m)
  obtain ⟨J, g, hJ, hg, hfg⟩ := hC _ (kaneFun e S) (kaneFun_monotone e S)
  -- the junta is small
  have hJt : 64 * J.card ≤ 2 ^ t := by
    have h1 : booleanDegree (kaneFun e S) + 2 ≤ t * t + 3 := by
      have := booleanDegree_kaneFun e S
      omega
    calc 64 * J.card ≤ 64 * (t * t + 3) ^ C := by
          gcongr
          exact hJ.trans (Nat.pow_le_pow_left h1 C)
      _ ≤ 2 ^ t := htC
  -- the second-moment bound
  have hcount := kane_count e S J g hg
  set B := (univ.filter fun z => kaneFun e S z ≠ g z).card
  -- real parameters
  have hW : (2 : ℝ) ^ t = 8 * m := by
    have : 2 ^ t = 2 ^ (t - 3) * 2 ^ 3 := by rw [← pow_add]; congr 1; omega
    rw [hm]
    exact_mod_cast (show 2 ^ t = 8 * 2 ^ (t - 3) by rw [this]; ring)
  have hM : (0 : ℝ) < m := by rw [hm]; positivity
  have hP : (0 : ℝ) < 2 ^ Fintype.card ((Fin t × Fin t) ⊕ Fin m) := by positivity
  have hD : (pairSum S : ℝ) ≤ m * 2 ^ t + 3 * m ^ 2 := by
    have h1 : ((t : ℝ) ^ t) * pairSum S ≤ m * t ^ t * 2 ^ t + m ^ 2 * (t + 1) ^ t := by
      exact_mod_cast hS
    have h2 := succ_pow_le_three_mul t ht0
    have htt : (0 : ℝ) < (t : ℝ) ^ t := by positivity
    have h3 : ((t : ℝ) ^ t) * pairSum S ≤ (t : ℝ) ^ t * (m * 2 ^ t + 3 * m ^ 2) := by
      nlinarith
    exact le_of_mul_le_mul_left h3 htt
  have hJ' : (64 : ℝ) * J.card ≤ 2 ^ t := by exact_mod_cast hJt
  rw [hW] at hcount hD hJ'
  -- `16 m² - D - 8 m |J| ≥ 4 m²`
  have hJm : (8 : ℝ) * m * J.card ≤ m ^ 2 := by nlinarith
  have hlow : (4 : ℝ) * m ^ 2 ≤ 2 * m * (8 * m) - pairSum S - J.card * (8 * m) := by
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hlow hP.le
  have hB : (4 : ℝ) * m ^ 2 * 2 ^ Fintype.card ((Fin t × Fin t) ⊕ Fin m) ≤
      128 * m ^ 2 * B := by
    nlinarith
  have hB' : (2 : ℝ) ^ Fintype.card ((Fin t × Fin t) ⊕ Fin m) ≤ 32 * B := by
    have hm2 : (0 : ℝ) < 4 * m ^ 2 := by positivity
    nlinarith
  have hfg' : (B : ℝ) ≤ 1 / 64 * 2 ^ Fintype.card ((Fin t × Fin t) ⊕ Fin m) := hfg
  linarith

end MathlibExt.Combinatorics.MonotoneJuntaApproximationAMR127Problem0022Wanted
