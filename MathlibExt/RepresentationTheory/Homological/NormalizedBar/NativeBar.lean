/-
Copyright (c) 2022 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: @toskua
-/
module

public import MathlibExt.RepresentationTheory.Homological.NormalizedBar.Quotient
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Comparison with the native inhomogeneous bar resolution

The literal normalized model maps to and from the actual native bar
complex through its native standard-complex isomorphism. The inverse
basis calculation follows the existing calculation in the native
d_comp_diagonalSuccIsoFree_inv_eq proof.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory
open scoped MonoidAlgebra

namespace Rep.NormalizedBar

universe u

variable (k G : Type u) [CommRing k] [Group G]

/-- Actual inverse of the native homogeneous/inhomogeneous basis isomorphism. -/
theorem nativeDiagonalInverse_single (n : ℕ) (g : Fin n → G) (h : G) (r : k) :
    (Rep.diagonalSuccIsoFree k G n).inv.hom
      (Finsupp.single g (MonoidAlgebra.single h r)) =
        MonoidAlgebra.single (h • Fin.partialProd g) r := by
  simp only [Rep.diagonalSuccIsoFree, Rep.diagonalSuccIsoTensorTrivial, Iso.trans_inv,
    Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
  have step : (Rep.leftRegularTensorTrivialIsoFree k G (Fin n → G)).inv.hom
      (Finsupp.single g (MonoidAlgebra.single h r)) =
        MonoidAlgebra.single h 1 ⊗ₜ[k] MonoidAlgebra.single g r :=
    Representation.leftRegularTensorTrivialIsoFree_symm_apply_single_single g h r
  rw [step]
  simp only [Action.tensorObj_V, Rep.tensor_V, Rep.tensor_ρ]
  have hmap := Representation.linearizeMap_single (k := k)
    (Action.diagonalSuccIsoTensorTrivial G n).inv (h, g) ((1 : k) * r)
  have hmu := Representation.LinearizeMonoidal.μ_apply_single_single (k := k)
    (X := Action.leftRegular G) (Y := Action.trivial G (Fin n → G)) h g 1 r
  have hinv : (Action.diagonalSuccIsoTensorTrivial G n).inv.hom (h, g) =
      h • Fin.partialProd g :=
    Action.diagonalSuccIsoTensorTrivial_inv_hom_apply h g
  exact ((congrArg (fun z => Representation.linearizeMap
    (Action.diagonalSuccIsoTensorTrivial G n).inv z) hmu).trans hmap).trans (by
      simpa only [one_mul] using
        congrArg (fun a : Fin (n + 1) → G =>
          (MonoidAlgebra.single a r : k[Fin (n + 1) → G])) hinv)

/-- The native bar/standard complex comparison on the actual basis symbols. -/
@[simp]
theorem nativeBarToStandard_single (n : ℕ) (g : Fin n → G) (h : G) (r : k) :
    ((Rep.barComplex.isoStandardComplex k G).hom.f n).hom
      (Finsupp.single g (MonoidAlgebra.single h r)) =
        standardSymbol k G n (h • Fin.partialProd g) r :=
  nativeDiagonalInverse_single k G n g h r

/-- The native bar-to-standard map and actual full tuple basis comparison
are mutually inverse in each degree. -/
@[simp, reassoc]
theorem nativeBarToStandard_comp_basisIso (n : ℕ) :
    (Rep.barComplex.isoStandardComplex k G).hom.f n ≫ (basisIso k G n).hom =
      𝟙 (fullDegree k G n) := by
  refine Rep.free_ext k G _ _ _ ?_
  intro g
  change (basisIso k G n).hom.hom
      (((Rep.barComplex.isoStandardComplex k G).hom.f n).hom
        (Finsupp.single g (MonoidAlgebra.single 1 1))) =
    Finsupp.single g (MonoidAlgebra.single 1 1)
  rw [nativeBarToStandard_single, basisIso_hom_single]
  simp [Fin.partialProd_right_inv, Fin.partialProd_zero]

/-- Canonical quotient projection from the actual native bar complex. -/
def nativeProjection : Rep.barComplex k G ⟶ complex k G :=
  (Rep.barComplex.isoStandardComplex k G).hom ≫ projection k G

/-- Canonical normalization-corrected chain section into the native bar complex. -/
def nativeInclusion : complex k G ⟶ Rep.barComplex k G :=
  inclusion k G ≫ (Rep.barComplex.isoStandardComplex k G).inv

@[reassoc (attr := simp)]
theorem nativeInclusion_comp_nativeProjection :
    nativeInclusion k G ≫ nativeProjection k G = 𝟙 (complex k G) := by
  let e : Rep.barComplex k G ≅ Rep.standardComplex k G :=
    Rep.barComplex.isoStandardComplex k G
  let i : complex k G ⟶ Rep.standardComplex k G := by
    change complex k G ⟶ standardComplex k G
    exact inclusion k G
  let p : Rep.standardComplex k G ⟶ complex k G := by
    change standardComplex k G ⟶ complex k G
    exact projection k G
  have hcancel : e.inv ≫ (e.hom ≫ p) = p :=
    Eq.trans (Category.assoc e.inv e.hom p).symm
      (Eq.trans
        (congrArg (fun f : Rep.standardComplex k G ⟶ Rep.standardComplex k G =>
          f ≫ p) e.inv_hom_id)
        (Category.id_comp p))
  have hsplit : i ≫ p = 𝟙 (complex k G) := by
    change inclusion k G ≫ projection k G = 𝟙 (complex k G)
    exact inclusion_comp_projection k G
  change (i ≫ e.inv) ≫ (e.hom ≫ p) = 𝟙 (complex k G)
  exact Eq.trans (Category.assoc i e.inv (e.hom ≫ p))
    (Eq.trans
      (congrArg (fun f : Rep.standardComplex k G ⟶ complex k G => i ≫ f) hcancel)
      hsplit)

@[simp]
theorem nativeProjection_f (n : ℕ) :
    (nativeProjection k G).f n = rawProjection k G n := by
  let e : Rep.barComplex k G ≅ Rep.standardComplex k G :=
    Rep.barComplex.isoStandardComplex k G
  let p : Rep.standardComplex k G ⟶ complex k G := by
    change standardComplex k G ⟶ complex k G
    exact projection k G
  let b : (Rep.standardComplex k G).X n ≅ fullDegree k G n := by
    change (standardSimplicial k G).obj (Opposite.op (SimplexCategory.mk n)) ≅ fullDegree k G n
    exact basisIso k G n
  let r : fullDegree k G n ⟶ (complex k G).X n := by
    change fullDegree k G n ⟶ degree k G n
    exact rawProjection k G n
  have hf : (e.hom ≫ p).f n = e.hom.f n ≫ p.f n :=
    HomologicalComplex.comp_f e.hom p n
  have hp : p.f n = b.hom ≫ r := by
    change (projection k G).f n = standardProjection k G n
    exact projection_f k G n
  have hb : e.hom.f n ≫ b.hom = 𝟙 (fullDegree k G n) := by
    change (Rep.barComplex.isoStandardComplex k G).hom.f n ≫
      (basisIso k G n).hom = 𝟙 (fullDegree k G n)
    exact nativeBarToStandard_comp_basisIso k G n
  have hassoc : e.hom.f n ≫ (b.hom ≫ r) = (e.hom.f n ≫ b.hom) ≫ r :=
    (Category.assoc (e.hom.f n) b.hom r).symm
  have hid : (e.hom.f n ≫ b.hom) ≫ r = r :=
    Eq.trans
      (congrArg (fun f : fullDegree k G n ⟶ fullDegree k G n => f ≫ r) hb)
      (Category.id_comp r)
  change (e.hom ≫ p).f n = r
  exact Eq.trans hf
    (Eq.trans
      (congrArg (fun f : (Rep.standardComplex k G).X n ⟶ (complex k G).X n =>
        e.hom.f n ≫ f) hp)
      (Eq.trans hassoc hid))

/-- Normalization is a homotopy equivalence with the actual native bar complex. -/
def homotopyEquivNativeBar : HomotopyEquiv (complex k G) (Rep.barComplex k G) :=
  (homotopyEquivStandard k G).trans
    (HomotopyEquiv.ofIso (Rep.barComplex.isoStandardComplex k G).symm)

/-- The actual normalization homotopy equivalence induces the homology comparison. -/
def homologyIsoNativeBar (n : ℕ) :
    (complex k G).homology n ≅ (Rep.barComplex k G).homology n :=
  (homotopyEquivNativeBar k G).toHomologyIso n

/-- The literal normalized model as an actual projective resolution,
with the native augmentation composed with the corrected chain inclusion. -/
def resolution : ProjectiveResolution (Rep.trivial k G k) where
  complex := complex k G
  projective n := complex_X_projective k G n
  π := nativeInclusion k G ≫ (Rep.barResolution k G).π
  quasiIso := by
    let f : complex k G ⟶ Rep.barComplex k G := nativeInclusion k G
    let p : Rep.barComplex k G ⟶
        (ChainComplex.single₀ (Rep k G)).obj (Rep.trivial k G k) := by
      change (Rep.barResolution k G).complex ⟶
        (ChainComplex.single₀ (Rep k G)).obj (Rep.trivial k G k)
      exact (Rep.barResolution k G).π
    have hf : QuasiIso f := by
      change QuasiIso ((homotopyEquivNativeBar k G).hom)
      exact (homotopyEquivNativeBar k G).quasiIso_hom
    have hp : QuasiIso p := by
      change QuasiIso ((Rep.barResolution k G).π)
      exact (Rep.barResolution k G).quasiIso
    change QuasiIso (f ≫ p)
    exact _root_.quasiIso_comp f p (hφ := hf) (hφ' := hp)

/-- The actual degeneracy subcomplex in the native inhomogeneous presentation. -/
abbrev nativeDegeneracyComplex : ChainComplex (Rep k G) ℕ :=
  CategoryTheory.Limits.kernel (nativeProjection k G)

/-- Its actual chain inclusion. -/
abbrev nativeDegeneracyInclusion : nativeDegeneracyComplex k G ⟶ Rep.barComplex k G :=
  CategoryTheory.Limits.kernel.ι (nativeProjection k G)

instance nativeProjection_epi : Epi (nativeProjection k G) :=
  epi_of_epi_fac (nativeInclusion_comp_nativeProjection k G)

/-- The native inhomogeneous degeneracy quotient is the literal normalized model. -/
def nativeQuotientIso :
    CategoryTheory.Limits.cokernel (nativeDegeneracyInclusion k G) ≅ complex k G :=
  asIso (Abelian.factorThruCoimage (nativeProjection k G))

@[reassoc (attr := simp)]
theorem nativeQuotientIso_factor :
    CategoryTheory.Limits.cokernel.π (nativeDegeneracyInclusion k G) ≫
        (nativeQuotientIso k G).hom = nativeProjection k G :=
  Abelian.coimage.fac (nativeProjection k G)

/-- The native bar quotient kills exactly the source's degenerate-symbol span. -/
theorem nativeProjection_f_kernel_iff (n : ℕ) (x : (fullDegree k G n).V) :
    ((nativeProjection k G).f n).hom x = 0 ↔ x ∈ degenerateDegree k G n := by
  rw [nativeProjection_f]
  exact rawProjection_eq_zero_iff k G n x

end Rep.NormalizedBar

end
