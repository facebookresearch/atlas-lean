/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.RevealedPreference.GARP
public import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.DotProduct

@[expose] public section

/-!
# Revealed preference: Afriat certificates rationalize the data

An Afriat certificate for demand data `(pⁱ, xⁱ)` is a family of numbers `Uⁱ` and `λⁱ > 0` with
`Uⁱ ≤ Uʲ + λʲ pʲ·(xⁱ - xʲ)` for all observations `i, j`. Afriat's utility
`U(x) = minᵢ (Uⁱ + λⁱ pⁱ·(x - xⁱ))` built from a certificate is locally nonsatiated, continuous,
concave and monotone when all prices are strictly positive, takes the value `Uⁱ` at `xⁱ`, and
rationalizes the data. This is direction (3) ⇒ (4) of Afriat's theorem.

## Main definitions

* `DemandData.IsAfriatCertificate`: Afriat's inequalities with positive multipliers.
* `DemandData.afriatUtility`: the lower envelope of the affine functions
  `x ↦ Uⁱ + λⁱ pⁱ·(x - xⁱ)`.

## Main results

* `DemandData.IsAfriatCertificate.afriatUtility_spec`: Afriat's theorem, (3) ⇒ (4).

## References

* H. R. Varian, "The Nonparametric Approach to Demand Analysis", Econometrica 50 (1982),
  945-973: Afriat's theorem p. 946; proof of (3) ⇒ (4) in Appendix I.
-/

namespace MathlibExt.Economics.RevealedPreference

namespace DemandData

/-- Afriat's inequalities (Varian 1982, Afriat's theorem (3)): numbers `Uⁱ` and `λⁱ > 0` with
`Uⁱ ≤ Uʲ + λʲ pʲ·(xⁱ - xʲ)` for all observations `i, j`. -/
def IsAfriatCertificate {ι G : Type*} [Fintype G] (D : DemandData ι G) (U lam : ι → ℝ) :
    Prop :=
  (∀ i, 0 < lam i) ∧
    ∀ i j, U i ≤ U j + lam j * (D.price j ⬝ᵥ (D.bundle i - D.bundle j))

/-- Afriat's utility function `U(x) = minᵢ (Uⁱ + λⁱ pⁱ·(x - xⁱ))` (Varian 1982, Appendix I,
proof of (3) ⇒ (4)). -/
noncomputable def afriatUtility {ι G : Type*} [Fintype ι] [Nonempty ι] [Fintype G]
    (D : DemandData ι G) (U lam : ι → ℝ) (x : G → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty
    (fun i => U i + lam i * (D.price i ⬝ᵥ (x - D.bundle i)))

end DemandData

/-- Afriat's theorem, (3) ⇒ (4): with strictly positive prices, Afriat's utility built from a
certificate is locally nonsatiated, continuous, concave and monotone, takes the value `Uⁱ` at
`xⁱ`, and rationalizes the data. -/
theorem DemandData.IsAfriatCertificate.afriatUtility_spec {ι G : Type*} [Fintype ι]
    [Nonempty ι] [Fintype G] [Nonempty G] {D : DemandData ι G} {U lam : ι → ℝ}
    (hp : ∀ i g, 0 < D.price i g) (h : D.IsAfriatCertificate U lam) :
    LocallyNonsatiated (D.afriatUtility U lam) ∧ Continuous (D.afriatUtility U lam) ∧
      ConcaveOn ℝ Set.univ (D.afriatUtility U lam) ∧ Monotone (D.afriatUtility U lam) ∧
      (∀ i, D.afriatUtility U lam (D.bundle i) = U i) ∧ D.Rationalizes (D.afriatUtility U lam) := by
  obtain ⟨hlam, hcert⟩ := h
  have hval : ∀ i, D.afriatUtility U lam (D.bundle i) = U i := by
    intro i
    unfold DemandData.afriatUtility
    apply le_antisymm
    · have hle : Finset.univ.inf' Finset.univ_nonempty
          (fun j => U j + lam j * (D.price j ⬝ᵥ (D.bundle i - D.bundle j)))
          ≤ U i + lam i * (D.price i ⬝ᵥ (D.bundle i - D.bundle i)) :=
        Finset.inf'_le _ (Finset.mem_univ i)
      have hzero : D.price i ⬝ᵥ (D.bundle i - D.bundle i) = 0 := by
        rw [sub_self, dotProduct_zero]
      rw [hzero, mul_zero, add_zero] at hle
      exact hle
    · apply Finset.le_inf'
      intro j _
      exact hcert i j
  have hrat : D.Rationalizes (D.afriatUtility U lam) := by
    intro i y hy
    unfold DemandData.afriatUtility
    have hle : Finset.univ.inf' Finset.univ_nonempty
          (fun j => U j + lam j * (D.price j ⬝ᵥ (y - D.bundle j)))
          ≤ U i + lam i * (D.price i ⬝ᵥ (y - D.bundle i)) :=
      Finset.inf'_le _ (Finset.mem_univ i)
    have hdiff : D.price i ⬝ᵥ (y - D.bundle i) ≤ 0 := by
      rw [dotProduct_sub]
      exact sub_nonpos.mpr hy
    have hmul : lam i * (D.price i ⬝ᵥ (y - D.bundle i)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt (hlam i)) hdiff
    have hterm : U i + lam i * (D.price i ⬝ᵥ (y - D.bundle i)) ≤ U i := by
      linarith
    have hval' : Finset.univ.inf' Finset.univ_nonempty
          (fun j => U j + lam j * (D.price j ⬝ᵥ (D.bundle i - D.bundle j))) = U i := hval i
    rw [hval']
    exact le_trans hle hterm
  have hcont : Continuous (D.afriatUtility U lam) := by
    have hterm : ∀ i : ι, Continuous
        (fun x : G → ℝ => U i + lam i * (D.price i ⬝ᵥ (x - D.bundle i))) := by
      intro i
      have hsub : Continuous (fun x : G → ℝ => x - D.bundle i) :=
        continuous_id.sub continuous_const
      have hdot : Continuous (fun x : G → ℝ => D.price i ⬝ᵥ (x - D.bundle i)) :=
        continuous_const.dotProduct hsub
      exact continuous_const.add (continuous_const.mul hdot)
    have h := Continuous.finset_inf'_apply (s := Finset.univ)
      (f := fun (i : ι) (x : G → ℝ) => U i + lam i * (D.price i ⬝ᵥ (x - D.bundle i)))
      Finset.univ_nonempty (fun i _ => hterm i)
    exact h
  have hconc : ConcaveOn ℝ Set.univ (D.afriatUtility U lam) := by
    have htermconc : ∀ i : ι, ConcaveOn ℝ Set.univ
        (fun x : G → ℝ => U i + lam i * (D.price i ⬝ᵥ (x - D.bundle i))) := by
      intro i
      constructor
      · exact convex_univ
      · intro x _ y _ a b ha hb hab
        have hdot : D.price i ⬝ᵥ ((a • x + b • y) - D.bundle i)
            = a * (D.price i ⬝ᵥ x) + b * (D.price i ⬝ᵥ y) - D.price i ⬝ᵥ D.bundle i := by
          rw [dotProduct_sub, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul,
            smul_eq_mul]
        have heq : U i + lam i * (D.price i ⬝ᵥ ((a • x + b • y) - D.bundle i))
            = a * (U i + lam i * (D.price i ⬝ᵥ (x - D.bundle i)))
              + b * (U i + lam i * (D.price i ⬝ᵥ (y - D.bundle i))) := by
          rw [hdot, dotProduct_sub, dotProduct_sub]
          linear_combination (lam i * (D.price i ⬝ᵥ D.bundle i) - U i) * hab
        rw [smul_eq_mul, smul_eq_mul]
        exact le_of_eq heq.symm
    constructor
    · exact convex_univ
    · intro x _ y _ a b ha hb hab
      change a • D.afriatUtility U lam x + b • D.afriatUtility U lam y
        ≤ D.afriatUtility U lam (a • x + b • y)
      unfold DemandData.afriatUtility
      apply Finset.le_inf'
      intro i _
      obtain ⟨-, hconc⟩ := htermconc i
      have hc := hconc (Set.mem_univ x) (Set.mem_univ y) ha hb hab
      simp only at hc
      have hfx : Finset.univ.inf' Finset.univ_nonempty
            (fun j => U j + lam j * (D.price j ⬝ᵥ (x - D.bundle j)))
            ≤ U i + lam i * (D.price i ⬝ᵥ (x - D.bundle i)) :=
        Finset.inf'_le _ (Finset.mem_univ i)
      have hfy : Finset.univ.inf' Finset.univ_nonempty
            (fun j => U j + lam j * (D.price j ⬝ᵥ (y - D.bundle j)))
            ≤ U i + lam i * (D.price i ⬝ᵥ (y - D.bundle i)) :=
        Finset.inf'_le _ (Finset.mem_univ i)
      rw [smul_eq_mul, smul_eq_mul] at hc ⊢
      have ha' : a * (Finset.univ.inf' Finset.univ_nonempty
            (fun j => U j + lam j * (D.price j ⬝ᵥ (x - D.bundle j))))
            ≤ a * (U i + lam i * (D.price i ⬝ᵥ (x - D.bundle i))) :=
        mul_le_mul_of_nonneg_left hfx ha
      have hb' : b * (Finset.univ.inf' Finset.univ_nonempty
            (fun j => U j + lam j * (D.price j ⬝ᵥ (y - D.bundle j))))
            ≤ b * (U i + lam i * (D.price i ⬝ᵥ (y - D.bundle i))) :=
        mul_le_mul_of_nonneg_left hfy hb
      exact le_trans (add_le_add ha' hb') hc
  have hmono : Monotone (D.afriatUtility U lam) := by
    intro x y hxy
    unfold DemandData.afriatUtility
    apply Finset.le_inf'
    intro i _
    have h1 : D.afriatUtility U lam x ≤ U i + lam i * (D.price i ⬝ᵥ (x - D.bundle i)) := by
      unfold DemandData.afriatUtility
      exact Finset.inf'_le _ (Finset.mem_univ i)
    have hprice : (0 : G → ℝ) ≤ D.price i := fun g => le_of_lt (hp i g)
    have hdot : D.price i ⬝ᵥ x ≤ D.price i ⬝ᵥ y :=
      dotProduct_le_dotProduct_of_nonneg_left hxy hprice
    have hsub : D.price i ⬝ᵥ (x - D.bundle i) ≤ D.price i ⬝ᵥ (y - D.bundle i) := by
      rw [dotProduct_sub, dotProduct_sub]
      exact sub_le_sub_right hdot _
    have hmul : lam i * (D.price i ⬝ᵥ (x - D.bundle i))
        ≤ lam i * (D.price i ⬝ᵥ (y - D.bundle i)) :=
      mul_le_mul_of_nonneg_left hsub (le_of_lt (hlam i))
    have h2 : U i + lam i * (D.price i ⬝ᵥ (x - D.bundle i))
        ≤ U i + lam i * (D.price i ⬝ᵥ (y - D.bundle i)) := by
      gcongr
    exact le_trans h1 h2
  have hns : LocallyNonsatiated (D.afriatUtility U lam) := by
    intro y ε hε
    set c : G → ℝ := fun _ => ε / 2 with hc
    refine ⟨y + c, ?_, ?_⟩
    · rw [dist_pi_lt_iff hε]
      intro b
      have hb : (y + c) b = y b + ε / 2 := by simp [hc]
      rw [hb, Real.dist_eq]
      have hsub : y b + ε / 2 - y b = ε / 2 := by ring
      rw [hsub, abs_of_pos (half_pos hε)]
      linarith
    · obtain ⟨j, hj, h_eq⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
        (fun i => U i + lam i * (D.price i ⬝ᵥ ((y + c) - D.bundle i)))
      have hfy : D.afriatUtility U lam y
          ≤ U j + lam j * (D.price j ⬝ᵥ (y - D.bundle j)) := by
        unfold DemandData.afriatUtility
        exact Finset.inf'_le _ (Finset.mem_univ j)
      have hzy : (y + c) - y = c := add_sub_cancel_left y c
      have hpos : 0 < D.price j ⬝ᵥ ((y + c) - y) := by
        rw [hzy]
        unfold dotProduct
        simp only [hc]
        exact Finset.sum_pos (fun g _ => mul_pos (hp j g) (half_pos hε))
          Finset.univ_nonempty
      have hfun : (y + c) - D.bundle j
          = (y - D.bundle j) + ((y + c) - y) := by
        ext g
        simp
        ring
      have hlt : D.price j ⬝ᵥ (y - D.bundle j)
          < D.price j ⬝ᵥ ((y + c) - D.bundle j) := by
        rw [hfun, dotProduct_add]
        exact lt_add_of_pos_right _ hpos
      have hterm : U j + lam j * (D.price j ⬝ᵥ (y - D.bundle j))
          < U j + lam j * (D.price j ⬝ᵥ ((y + c) - D.bundle j)) := by
        have h1 := mul_lt_mul_of_pos_left hlt (hlam j)
        linarith
      have hfz : U j + lam j * (D.price j ⬝ᵥ ((y + c) - D.bundle j))
          = D.afriatUtility U lam (y + c) := by
        unfold DemandData.afriatUtility
        exact h_eq.symm
      exact lt_of_le_of_lt hfy (lt_of_lt_of_eq hterm hfz)
  exact ⟨hns, hcont, hconc, hmono, hval, hrat⟩

end MathlibExt.Economics.RevealedPreference
