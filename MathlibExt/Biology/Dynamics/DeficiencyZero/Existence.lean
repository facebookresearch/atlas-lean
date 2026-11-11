/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.ComplexBalanced
public import Mathlib.Logic.Relation
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Deficiency zero: existence of a complex-balanced equilibrium

For a mass-action reaction network (`ReactionNetwork`, from
`MathlibExt.Biology.Dynamics.ComplexBalanced`) that is weakly reversible and has deficiency
zero, every choice of positive rate constants admits a positive complex-balanced equilibrium
(Horn 1972; Feinberg 1972). Combined with the Horn–Jackson theorem
`existsUnique_equilibrium_of_isComplexBalanced`, already proved for any network with one
positive complex-balanced equilibrium, this gives the weakly reversible half of the
deficiency-zero theorem: exactly one positive equilibrium in each positive stoichiometric
compatibility class.

The proof has two steps.

1. *Weak reversibility.* The Laplacian of the weighted reaction graph on the complexes
   reachable from a complex `z₀` has columns summing to `0`, so it is singular. Its
   off-diagonal entries are nonnegative, so the absolute value of a kernel vector is again a
   kernel vector. Under weak reversibility its zero set is closed under directed reaction
   paths, so it is positive at `z₀`. Summing over `z₀` gives a positive vector `ψ` with inflow
   equal to outflow at every complex.
2. *Deficiency zero.* Solve the log-linear system `⟨prod r - src r, μ⟩ = log ψ (prod r) -
   log ψ (src r)` for `μ : S → ℝ`; it is solvable because, by deficiency zero, every relation
   among the reaction vectors is a relation among the complex differences
   (`LinearMap.range_dualMap_eq_dualAnnihilator_ker`). Then `c = exp μ` has
   `c ^ y / ψ y` constant along every reaction, hence is complex balanced.

## Main results

* `exists_pos_isComplexBalanced_of_balanced_weights`: deficiency zero and a positive vector
  balancing the weighted reaction graph give a positive complex-balanced concentration.
* `exists_pos_isComplexBalanced_of_deficiency_zero`: weak reversibility, deficiency zero and
  positive rate constants give a positive complex-balanced equilibrium.
* `existsUnique_equilibrium_of_deficiency_zero`: under the same hypotheses each positive
  stoichiometric compatibility class contains exactly one positive equilibrium.

## Form of the hypotheses

The complexes, linkage classes, `deficiency` and `IsWeaklyReversible` of a network are not
part of the production API that this file imports, so both network hypotheses are stated in
elementary form. Weak reversibility is written out as a `Relation.ReflTransGen` hypothesis (it
unfolds to `IsWeaklyReversible` from `WantedExt.Biology.Dynamics.DeficiencyZeroWanted`).
Deficiency zero is stated as `ker Y ∩ im ∂ = 0`: every weighting `α` of the reactions with
`∑ α r (prod r - src r) = 0` satisfies `∑ α r (η (prod r) - η (src r)) = 0` for every function
`η` on complexes. It is equivalent to `δ = n - ℓ - s = 0` via the rank identity
`dim im ∂ = n - ℓ`, which is not proved here. The non-weakly-reversible half of the theorem,
stability and non-mass-action kinetics are not covered.

## References

* F. Horn, "Necessary and sufficient conditions for complex balancing in chemical kinetics",
  Arch. Rational Mech. Anal. 49 (1972) 172–186.
* M. Feinberg, "Complex balancing in general kinetic systems", Arch. Rational Mech. Anal. 49
  (1972) 187–194.
* M. Feinberg, "Chemical reaction network structure and the stability of complex isothermal
  reactors — I. The deficiency zero and deficiency one theorems", Chem. Eng. Sci. 42 (1987)
  2229–2268.
* M. Feinberg, *Foundations of Chemical Reaction Network Theory*, Springer (2019).
-/

@[expose] public section

open Finset Real Matrix

namespace MathlibExt.Biology.Dynamics.ComplexBalanced

variable {S ρ : Type*}

namespace ReactionNetwork

variable (N : ReactionNetwork S ρ)

/-- Under the deficiency-zero hypothesis, the log-linear system
`⟨prod r - src r, μ⟩ = η (prod r) - η (src r)` has a solution `μ` for every `η`. -/
private theorem exists_log_solution [Fintype S] [Fintype ρ]
    (hδ : ∀ α : ρ → ℝ, ∑ r, α r • (fun s => (N.prod r s : ℝ) - N.src r s) = 0 →
      ∀ η : (S → ℕ) → ℝ, ∑ r, α r * (η (N.prod r) - η (N.src r)) = 0)
    (η : (S → ℕ) → ℝ) :
    ∃ μ : S → ℝ, ∀ r, ∑ s, ((N.prod r s : ℝ) - N.src r s) * μ s =
      η (N.prod r) - η (N.src r) := by
  classical
  let v : ρ → S → ℝ := fun r s => (N.prod r s : ℝ) - N.src r s
  let f : (ρ → ℝ) →ₗ[ℝ] (S → ℝ) := Fintype.linearCombination ℝ v
  let β : Module.Dual ℝ (ρ → ℝ) :=
    Fintype.linearCombination ℝ fun r => η (N.prod r) - η (N.src r)
  have hβ : β ∈ (LinearMap.ker f).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro α hα
    rw [LinearMap.mem_ker, Fintype.linearCombination_apply] at hα
    simpa [β, Fintype.linearCombination_apply, smul_eq_mul] using hδ α hα η
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hβ
  obtain ⟨φ, hφ⟩ := hβ
  refine ⟨fun s => φ (Pi.single s 1), fun r => ?_⟩
  have h := LinearMap.congr_fun hφ (Pi.single r 1)
  simp only [LinearMap.dualMap_apply, f, β, Fintype.linearCombination_apply_single,
    one_smul] at h
  rw [← h, pi_eq_sum_univ (v r), map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_smul, smul_eq_mul]
  change v r s * φ (Pi.single s 1) = _
  congr 2
  funext j
  simp [Pi.single_apply, eq_comm]

/-- **Horn's construction.** Suppose the network has deficiency zero, in the linear form
`ker Y ∩ im ∂ = 0`: every weighting `α` of the reactions whose net stoichiometric change
`∑ α r (prod r - src r)` vanishes also has zero net change on the complexes (tested against
every `η`). Then every positive vector `ψ` on the complexes balancing the weighted reaction
graph (inflow `∑_{prod r = z} k r ψ (src r)` equals outflow `∑_{src r = z} k r ψ (src r)` at
each complex `z`) is realized, up to a positive factor on each linkage class, by the mass-action
monomials of a positive concentration vector, which is therefore complex balanced. No sign
condition on `k` is needed here.

Source: Horn (1972); Feinberg (2019), ch. 16. -/
theorem exists_pos_isComplexBalanced_of_balanced_weights [Fintype S] [Fintype ρ]
    (hδ : ∀ α : ρ → ℝ, ∑ r, α r • (fun s => (N.prod r s : ℝ) - N.src r s) = 0 →
      ∀ η : (S → ℕ) → ℝ, ∑ r, α r * (η (N.prod r) - η (N.src r)) = 0)
    {k : ρ → ℝ} {ψ : (S → ℕ) → ℝ} (hψ : ∀ r, 0 < ψ (N.src r) ∧ 0 < ψ (N.prod r))
    (hbal : ∀ z : S → ℕ, ∑ r ∈ univ.filter (fun r => N.src r = z), k r * ψ (N.src r) =
      ∑ r ∈ univ.filter (fun r => N.prod r = z), k r * ψ (N.src r)) :
    ∃ c : S → ℝ, (∀ s, 0 < c s) ∧ N.IsComplexBalanced k c := by
  obtain ⟨μ, hμ⟩ := N.exists_log_solution hδ fun z => Real.log (ψ z)
  let P : (S → ℕ) → ℝ := fun y => ∑ s, (y s : ℝ) * μ s
  let t : (S → ℕ) → ℝ := fun y => Real.exp (P y - Real.log (ψ y))
  have hrate : ∀ r, N.rate k (fun s => Real.exp (μ s)) r = k r * ψ (N.src r) * t (N.src r) := by
    intro r
    simp only [rate, t, P, Real.exp_sub, Real.exp_log (hψ r).1, ← Real.exp_nat_mul,
      ← Real.exp_sum]
    field_simp [(hψ r).1.ne']
  have ht : ∀ r, t (N.src r) = t (N.prod r) := by
    intro r
    have h := hμ r
    simp only [sub_mul, Finset.sum_sub_distrib] at h
    simp only [t, P]
    congr 1
    linarith
  refine ⟨fun s => Real.exp (μ s), fun s => Real.exp_pos _, fun z => ?_⟩
  calc ∑ r ∈ univ.filter (fun r => N.src r = z), N.rate k (fun s => Real.exp (μ s)) r
      = ∑ r ∈ univ.filter (fun r => N.src r = z), k r * ψ (N.src r) * t z :=
        Finset.sum_congr rfl fun r hr => by rw [hrate, (Finset.mem_filter.1 hr).2]
    _ = ∑ r ∈ univ.filter (fun r => N.prod r = z), k r * ψ (N.src r) * t z := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, hbal z]
    _ = ∑ r ∈ univ.filter (fun r => N.prod r = z), N.rate k (fun s => Real.exp (μ s)) r :=
        Finset.sum_congr rfl fun r hr => by rw [hrate, ht, (Finset.mem_filter.1 hr).2]

/-- For nonnegative weights balancing the reaction graph at positive rate constants, the zero
set is closed under predecessors: if the product of a reaction has weight `0`, so does its
source. -/
private theorem src_eq_zero_of_prod_eq_zero [Fintype S] [Fintype ρ] {k : ρ → ℝ} (hk : ∀ r, 0 < k r)
    {φ : (S → ℕ) → ℝ} (hφ : ∀ z, 0 ≤ φ z)
    (hbal : ∀ z : S → ℕ, ∑ r ∈ univ.filter (fun r => N.src r = z), k r * φ (N.src r) =
      ∑ r ∈ univ.filter (fun r => N.prod r = z), k r * φ (N.src r))
    {r : ρ} (h : φ (N.prod r) = 0) : φ (N.src r) = 0 := by
  have hz := hbal (N.prod r)
  rw [Finset.sum_eq_zero fun r' hr' => by rw [(Finset.mem_filter.1 hr').2, h, mul_zero],
    eq_comm, Finset.sum_eq_zero_iff_of_nonneg fun r' _ => mul_nonneg (hk r').le (hφ _)] at hz
  exact (mul_eq_zero.1 (hz r (Finset.mem_filter.2 ⟨mem_univ r, rfl⟩))).resolve_left
    (hk r).ne'

/-- In a weakly reversible network the zero set of nonnegative balancing weights is closed
under directed reaction paths. -/
private theorem eq_zero_of_reflTransGen [Fintype S] [Fintype ρ] {k : ρ → ℝ} (hk : ∀ r, 0 < k r)
    (hwr : ∀ r, Relation.ReflTransGen (fun y y' => ∃ r', N.src r' = y ∧ N.prod r' = y')
      (N.prod r) (N.src r))
    {φ : (S → ℕ) → ℝ} (hφ : ∀ z, 0 ≤ φ z)
    (hbal : ∀ z : S → ℕ, ∑ r ∈ univ.filter (fun r => N.src r = z), k r * φ (N.src r) =
      ∑ r ∈ univ.filter (fun r => N.prod r = z), k r * φ (N.src r))
    {a b : S → ℕ}
    (hab : Relation.ReflTransGen (fun y y' => ∃ r', N.src r' = y ∧ N.prod r' = y') a b)
    (ha : φ a = 0) : φ b = 0 := by
  have hsucc : ∀ r, φ (N.src r) = 0 → φ (N.prod r) = 0 := by
    intro r h0
    suffices ∀ a, Relation.ReflTransGen (fun y y' => ∃ r', N.src r' = y ∧ N.prod r' = y')
        a (N.src r) → φ a = 0 from this _ (hwr r)
    intro a har
    induction har using Relation.ReflTransGen.head_induction_on with
    | refl => exact h0
    | head hxy _ ih =>
      obtain ⟨r', rfl, rfl⟩ := hxy
      exact N.src_eq_zero_of_prod_eq_zero hk hφ hbal ih
  induction hab with
  | refl => exact ha
  | tail _ hbc ih =>
    obtain ⟨r, rfl, rfl⟩ := hbc
    exact hsucc r ih

/-- **Positive kernel of the Laplacian, one complex at a time.** For a weakly reversible
network with positive rate constants and any complex `z₀`, there are nonnegative weights on
the complexes that balance the weighted reaction graph and are positive at `z₀`. They come
from a kernel vector of the Laplacian of the set of complexes reachable from `z₀`: its columns
sum to `0`, so it is singular, and the absolute value of a kernel vector is again a kernel
vector because the off-diagonal entries are nonnegative. -/
private theorem exists_nonneg_balanced_pos [Fintype S] [Fintype ρ] {k : ρ → ℝ} (hk : ∀ r, 0 < k r)
    (hwr : ∀ r, Relation.ReflTransGen (fun y y' => ∃ r', N.src r' = y ∧ N.prod r' = y')
      (N.prod r) (N.src r))
    (z₀ : S → ℕ) :
    ∃ φ : (S → ℕ) → ℝ, (∀ z, 0 ≤ φ z) ∧ 0 < φ z₀ ∧
      ∀ z : S → ℕ, ∑ r ∈ univ.filter (fun r => N.src r = z), k r * φ (N.src r) =
        ∑ r ∈ univ.filter (fun r => N.prod r = z), k r * φ (N.src r) := by
  classical
  set R : (S → ℕ) → (S → ℕ) → Prop := fun y y' => ∃ r', N.src r' = y ∧ N.prod r' = y'
  -- The complexes reachable from `z₀`.
  let T : Finset (S → ℕ) :=
    (insert z₀ (univ.image N.prod)).filter (Relation.ReflTransGen R z₀)
  have hT : ∀ {x}, x ∈ T ↔ Relation.ReflTransGen R z₀ x := by
    intro x
    simp only [T, mem_filter, mem_insert, mem_image, mem_univ, true_and]
    refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, -, r, -, hr⟩
    · exact Or.inl h
    · exact Or.inr ⟨r, hr⟩
  have hclosed : ∀ r, N.src r ∈ T → N.prod r ∈ T := fun r h =>
    hT.2 ((hT.1 h).tail ⟨r, rfl, rfl⟩)
  have : Nonempty T := ⟨⟨z₀, hT.2 Relation.ReflTransGen.refl⟩⟩
  -- The Laplacian on `T`, acting on columns.
  let g : (S → ℕ) → (S → ℕ) → ℝ := fun a b => ∑ r, if N.src r = b then
    k r * ((if N.prod r = a then 1 else 0) - (if N.src r = a then 1 else 0)) else 0
  let M : Matrix T T ℝ := fun a b => g a b
  have hcol : ∀ b : T, ∑ a : T, M a b = 0 := by
    intro b
    rw [Finset.sum_coe_sort T (fun a => g a b)]
    simp only [g]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun r _ => ?_
    by_cases h : N.src r = b
    · simp only [h, ite_true]
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq,
        ite_eq_left (hclosed r (h ▸ b.2)), ite_eq_left b.2, sub_self, mul_zero]
    · simp [h]
  have hdet : M.det = 0 := Matrix.exists_vecMul_eq_zero_iff.1
    ⟨1, one_ne_zero, funext fun b => by simpa [Matrix.vecMul, dotProduct] using hcol b⟩
  obtain ⟨ψ, hψ0, hMψ⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hoff : ∀ a b : T, a ≠ b → 0 ≤ M a b := by
    intro a b hab
    refine Finset.sum_nonneg fun r _ => ?_
    by_cases h1 : N.src r = b
    · have h2 : ¬ N.src r = a := fun h2 => hab (Subtype.ext (h2.symm.trans h1))
      rw [ite_eq_left h1, ite_eq_right h2, sub_zero]
      split_ifs <;> simp [(hk r).le]
    · rw [ite_eq_right h1]
  -- The absolute value of `ψ` is again a kernel vector.
  let φ₀ : T → ℝ := fun a => |ψ a|
  have hrow : ∀ a, 0 ≤ (M *ᵥ φ₀) a := by
    intro a
    have h0 : ∑ b, M a b * ψ b = 0 := by simpa [Matrix.mulVec, dotProduct] using congrFun hMψ a
    have hdiag : M a a ≤ 0 := by
      have h := hcol a
      rw [← Finset.add_sum_erase _ _ (mem_univ a)] at h
      have : 0 ≤ ∑ a' ∈ univ.erase a, M a' a :=
        Finset.sum_nonneg fun a' ha' => hoff a' a (Finset.ne_of_mem_erase ha')
      linarith
    simp only [Matrix.mulVec, dotProduct, φ₀]
    rw [← Finset.add_sum_erase _ _ (mem_univ a)] at h0 ⊢
    have habs : |M a a * ψ a| ≤ ∑ b ∈ univ.erase a, M a b * |ψ b| := by
      rw [show M a a * ψ a = -∑ b ∈ univ.erase a, M a b * ψ b by linarith, abs_neg]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun b hb => ?_))
      rw [abs_mul, abs_of_nonneg (hoff a b (Finset.ne_of_mem_erase hb).symm)]
    rw [abs_mul, abs_of_nonpos hdiag] at habs
    linarith
  have hMφ : M *ᵥ φ₀ = 0 := by
    have hsum : ∑ a, (M *ᵥ φ₀) a = 0 := by
      simp only [Matrix.mulVec, dotProduct]
      rw [Finset.sum_comm]
      exact Finset.sum_eq_zero fun b _ => by rw [← Finset.sum_mul, hcol b, zero_mul]
    funext a
    exact (Finset.sum_eq_zero_iff_of_nonneg fun a _ => hrow a).1 hsum a (mem_univ a)
  -- Extend by zero off `T`.
  let φ : (S → ℕ) → ℝ := fun z => if h : z ∈ T then φ₀ ⟨z, h⟩ else 0
  have hφnn : ∀ z, 0 ≤ φ z := fun z => by
    simp only [φ]
    split_ifs <;> simp [φ₀]
  have hφT : ∀ z, z ∉ T → φ z = 0 := fun z h => dite_eq_right h
  have key : ∀ z, ∑ r, k r * φ (N.src r) *
      ((if N.prod r = z then 1 else 0) - (if N.src r = z then 1 else 0)) = 0 := by
    intro z
    by_cases hz : z ∈ T
    · have h : ∑ b : T, M ⟨z, hz⟩ b * φ₀ b = 0 := by
        simpa [Matrix.mulVec, dotProduct] using congrFun hMφ ⟨z, hz⟩
      have e : ∀ b : T, M ⟨z, hz⟩ b * φ₀ b = ∑ r, (if N.src r = b then
          k r * ((if N.prod r = z then 1 else 0) - (if N.src r = z then 1 else 0)) else 0) *
            φ₀ b := fun b => Finset.sum_mul _ _ _
      rw [Finset.sum_congr rfl fun b _ => e b, Finset.sum_comm] at h
      refine Eq.trans (Finset.sum_congr rfl fun r _ => ?_) h
      by_cases hr : N.src r ∈ T
      · rw [Fintype.sum_eq_single (⟨N.src r, hr⟩ : T) fun b hb =>
          by rw [ite_eq_right fun (h : N.src r = b) => hb (Subtype.ext h.symm), zero_mul]]
        rw [ite_eq_left rfl, show φ (N.src r) = φ₀ ⟨N.src r, hr⟩ from dite_eq_left hr]
        ring
      · rw [hφT _ hr, Fintype.sum_eq_zero _ fun b =>
          by rw [ite_eq_right fun (h : N.src r = b) => hr (h ▸ b.2), zero_mul]]
        ring
    · refine Finset.sum_eq_zero fun r _ => ?_
      by_cases hr : N.src r ∈ T
      · have h1 : N.prod r ≠ z := fun h => hz (h ▸ hclosed r hr)
        have h2 : N.src r ≠ z := fun h => hz (h ▸ hr)
        simp [h1, h2]
      · simp [hφT _ hr]
  have hφbal : ∀ z : S → ℕ, ∑ r ∈ univ.filter (fun r => N.src r = z), k r * φ (N.src r) =
      ∑ r ∈ univ.filter (fun r => N.prod r = z), k r * φ (N.src r) := by
    intro z
    have h := key z
    simp only [mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib, sub_eq_zero] at h
    rw [Finset.sum_filter, Finset.sum_filter]
    exact h.symm
  refine ⟨φ, hφnn, lt_of_le_of_ne (hφnn z₀) fun h0 => hψ0 ?_, hφbal⟩
  funext a
  have h := N.eq_zero_of_reflTransGen hk hwr hφnn hφbal (hT.1 a.2) h0.symm
  simpa [φ, φ₀, a.2] using h

/-- **Weak reversibility gives positive balancing weights.** For a weakly reversible network
with positive rate constants there are weights on the complexes, positive at every source and
product, that balance the weighted reaction graph: a positive vector in the kernel of the
Laplacian. -/
private theorem exists_pos_balanced_weights [Fintype S] [Fintype ρ] {k : ρ → ℝ}
    (hk : ∀ r, 0 < k r)
    (hwr : ∀ r, Relation.ReflTransGen (fun y y' => ∃ r', N.src r' = y ∧ N.prod r' = y')
      (N.prod r) (N.src r)) :
    ∃ ψ : (S → ℕ) → ℝ, (∀ r, 0 < ψ (N.src r) ∧ 0 < ψ (N.prod r)) ∧
      ∀ z : S → ℕ, ∑ r ∈ univ.filter (fun r => N.src r = z), k r * ψ (N.src r) =
        ∑ r ∈ univ.filter (fun r => N.prod r = z), k r * ψ (N.src r) := by
  choose φ hφnn hφpos hφbal using N.exists_nonneg_balanced_pos hk hwr
  let ψ : (S → ℕ) → ℝ := fun z => ∑ r', (φ (N.src r') z + φ (N.prod r') z)
  refine ⟨ψ, fun r => ⟨?_, ?_⟩, fun z => ?_⟩
  · have h := Finset.single_le_sum (f := fun r' => φ (N.src r') (N.src r) +
      φ (N.prod r') (N.src r)) (fun r' _ => add_nonneg (hφnn _ _) (hφnn _ _)) (mem_univ r)
    linarith [hφpos (N.src r), hφnn (N.prod r) (N.src r)]
  · have h := Finset.single_le_sum (f := fun r' => φ (N.src r') (N.prod r) +
      φ (N.prod r') (N.prod r)) (fun r' _ => add_nonneg (hφnn _ _) (hφnn _ _)) (mem_univ r)
    linarith [hφpos (N.prod r), hφnn (N.src r) (N.prod r)]
  · have e : ∀ F : Finset ρ, ∑ r ∈ F, k r * ψ (N.src r) = ∑ r', (∑ r ∈ F,
        k r * φ (N.src r') (N.src r) + ∑ r ∈ F, k r * φ (N.prod r') (N.src r)) := by
      intro F
      simp only [ψ, Finset.mul_sum, mul_add, ← Finset.sum_add_distrib]
      exact Finset.sum_comm
    rw [e, e]
    simp only [hφbal]

/-- **Deficiency-zero theorem, existence of a complex-balanced equilibrium** (Horn 1972;
Feinberg 1972). A weakly reversible mass-action network of deficiency zero has, for any
positive rate constants, a positive complex-balanced equilibrium.

The two network hypotheses are stated in elementary form. `hwr` is weak reversibility: for
every reaction `y → y'` there is a directed path of reactions from `y'` back to `y`. `hδ` is
deficiency zero in its linear-algebra form `ker Y ∩ im ∂ = 0` (Feinberg 2019, §6.4): a
weighting `α` of the reactions with zero net stoichiometric change `∑ α r (prod r - src r)`
has zero net change on the complexes. That `δ = n - ℓ - s = 0` is equivalent to `hδ` is the
rank identity `dim im ∂ = n - ℓ`, which is not proved here. Rate constants must be strictly
positive; zero rates are excluded.

Source: Horn (1972); Feinberg (1972); Feinberg (1987); Feinberg (2019), ch. 16. -/
theorem exists_pos_isComplexBalanced_of_deficiency_zero [Fintype S] [Fintype ρ]
    (hδ : ∀ α : ρ → ℝ, ∑ r, α r • (fun s => (N.prod r s : ℝ) - N.src r s) = 0 →
      ∀ η : (S → ℕ) → ℝ, ∑ r, α r * (η (N.prod r) - η (N.src r)) = 0)
    (hwr : ∀ r, Relation.ReflTransGen (fun y y' => ∃ r', N.src r' = y ∧ N.prod r' = y')
      (N.prod r) (N.src r))
    {k : ρ → ℝ} (hk : ∀ r, 0 < k r) :
    ∃ c : S → ℝ, (∀ s, 0 < c s) ∧ N.IsComplexBalanced k c := by
  obtain ⟨ψ, hψ, hbal⟩ := N.exists_pos_balanced_weights hk hwr
  exact N.exists_pos_isComplexBalanced_of_balanced_weights hδ hψ hbal

/-- **Deficiency-zero theorem, weakly reversible case** (Horn 1972; Horn & Jackson 1972;
Feinberg 1987). Under the hypotheses of `exists_pos_isComplexBalanced_of_deficiency_zero`,
each positive stoichiometric compatibility class `(x₀ + 𝒮) ∩ ℝ_{>0}^S`, `x₀ > 0`, contains
exactly one positive equilibrium of the mass-action system. The uniqueness half is the
Horn–Jackson theorem `existsUnique_equilibrium_of_isComplexBalanced`.

Source: Horn (1972); Horn & Jackson (1972); Feinberg (1987). -/
theorem existsUnique_equilibrium_of_deficiency_zero [Fintype S] [Fintype ρ]
    (hδ : ∀ α : ρ → ℝ, ∑ r, α r • (fun s => (N.prod r s : ℝ) - N.src r s) = 0 →
      ∀ η : (S → ℕ) → ℝ, ∑ r, α r * (η (N.prod r) - η (N.src r)) = 0)
    (hwr : ∀ r, Relation.ReflTransGen (fun y y' => ∃ r', N.src r' = y ∧ N.prod r' = y')
      (N.prod r) (N.src r))
    {k : ρ → ℝ} (hk : ∀ r, 0 < k r) {x₀ : S → ℝ} (hx₀ : ∀ s, 0 < x₀ s) :
    ∃! x : S → ℝ, (∀ s, 0 < x s) ∧ x - x₀ ∈ N.stoichiometricSubspace ∧
      N.massActionField k x = 0 := by
  obtain ⟨c, hc, hcb⟩ := N.exists_pos_isComplexBalanced_of_deficiency_zero hδ hwr hk
  exact N.existsUnique_equilibrium_of_isComplexBalanced hk hc hcb hx₀

end ReactionNetwork

end MathlibExt.Biology.Dynamics.ComplexBalanced
