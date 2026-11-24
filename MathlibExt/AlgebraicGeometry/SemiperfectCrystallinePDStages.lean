/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.RingTheory.SemiperfectCrystallineResidues
public import MathlibExt.AlgebraicGeometry.FullPDCrystallineTests

/-!
# The original finite A_cris objects on the full PD basis

Every underlying ring is the literal A_cris/(p^(n+1)), with its entire
residue kernel. Only the extension of divided powers to these fixed rings
is deferred. Their actual quotient maps, residue maps and geometric
crystalline arrows are defined here. No PD-ideal-adic completion enters.

Source: Scholze--Weinstein1211.6357v2, Proposition4.1.3 and Lemma4.1.8.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SemiperfectCrystallinePDStages

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.RingTheory.SemiperfectWittPDEnvelopes
open MathlibExt.RingTheory.SemiperfectCrystallineResidues
open FullPDCrystallineTests

variable (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [CharP R p]
  (A : UniversalEnvelope p R) (E : ResidueIdentification A)

/-- The original universal PD hull as the crystalline coefficient base. -/
abbrev hullPDBase : PDBase :=
  { ring := A.algebra.ring
    ideal := A.algebra.ideal
    dividedPowers := A.algebra.dividedPowers }

/-- Its reduced geometric base is the original R, with the original residue dictionary. -/
abbrev baseScheme : Over (hullPDBase p R A).reduction :=
  Over.mk (Spec.map (CommRingCat.ofHom E.equiv.toRingHom))

/-- Finite scalar multiplication comes from the original hull coefficient map. -/
@[instance_reducible] def finiteHullAlgebra (n : ℕ) :
    Algebra A.algebra.ring (FiniteRing p R A n) :=
  (finiteHullMap p R A n).toAlgebra

attribute [local instance] finiteHullAlgebra

/-- Divided powers on these fixed original rings and fixed p-power transitions. -/
structure PDStages where
  dividedPowers : ∀ n : ℕ, DividedPowers (finiteIdeal p R A E n)
  hull : ∀ n : ℕ, DividedPowers.IsDPMorphism A.algebra.dividedPowers
    (dividedPowers n) (finiteHullMap p R A n)
  transition : ∀ {n m : ℕ} (h : n ≤ m),
    DividedPowers.IsDPMorphism (dividedPowers m) (dividedPowers n)
      (finiteTransition p R A h)

variable (P : PDStages p R A E)

/-- The actual original finite crystalline object. Its PD ideal need not be nilpotent. -/
abbrev finiteTest (n : ℕ) : Obj p (hullPDBase p R A) (baseScheme p R A E) where
  ring := CommAlgCat.of A.algebra.ring (FiniteRing p R A n)
  ideal := finiteIdeal p R A E n
  dividedPowers := P.dividedPowers n
  baseCompatible := P.hull n
  pNilpotent := ⟨n + 1, finite_p_power p R A n⟩
  point := Spec.map (CommRingCat.ofHom (finiteResidueEquiv p R A E n).symm.toRingHom)
  pointBase := by
    change Spec.map (CommRingCat.ofHom (finiteResidueEquiv p R A E n).symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom E.equiv.toRingHom) =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap (finiteIdeal p R A E n)
        (finiteHullMap p R A n) (Ideal.map_le_iff_le_comap.mp (P.hull n).ideal_comp)))
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change (finiteResidueEquiv p R A E n).symm (hullResidue p R A E x) =
      Ideal.Quotient.mk (finiteIdeal p R A E n) (finiteHullMap p R A n x)
    rw [← finiteResidue_hull p R A E n x]
    exact RingHom.quotientKerEquivOfSurjective_symm_apply
      (finiteResidue_surjective p R A E n) (finiteHullMap p R A n x)

/-- The p-power quotient map is an algebra map for the same original hull coefficients. -/
abbrev finiteTransitionAlgebra {n m : ℕ} (h : n ≤ m) :
    (finiteTest p R A E P m).ring →ₐ[A.algebra.ring] (finiteTest p R A E P n).ring where
  __ := finiteTransition p R A h
  commutes' _ := rfl

/-- The original quotient-ring map on the full residue ideals. -/
def residueTransition {n m : ℕ} (h : n ≤ m) :
    (FiniteRing p R A m ⧸ finiteIdeal p R A E m) →+*
      (FiniteRing p R A n ⧸ finiteIdeal p R A E n) :=
  Ideal.quotientMap (finiteIdeal p R A E n) (finiteTransition p R A h)
    (Ideal.map_le_iff_le_comap.mp (P.transition h).ideal_comp)

/-- That quotient-ring map preserves the original R marking. -/
theorem residueTransition_point {n m : ℕ} (h : n ≤ m) :
    (residueTransition p R A E P h).comp (finiteResidueEquiv p R A E m).symm.toRingHom =
      (finiteResidueEquiv p R A E n).symm.toRingHom := by
  apply RingHom.ext
  intro r
  obtain ⟨x, rfl⟩ := finiteResidue_surjective p R A E m r
  change residueTransition p R A E P h
    ((finiteResidueEquiv p R A E m).symm (finiteResidue p R A E m x)) =
      (finiteResidueEquiv p R A E n).symm (finiteResidue p R A E m x)
  calc
    _ = residueTransition p R A E P h (Ideal.Quotient.mk (finiteIdeal p R A E m) x) :=
      congrArg (residueTransition p R A E P h)
        (RingHom.quotientKerEquivOfSurjective_symm_apply
          (finiteResidue_surjective p R A E m) x)
    _ = Ideal.Quotient.mk (finiteIdeal p R A E n) (finiteTransition p R A h x) := rfl
    _ = (finiteResidueEquiv p R A E n).symm
        (finiteResidue p R A E n (finiteTransition p R A h x)) :=
      (RingHom.quotientKerEquivOfSurjective_symm_apply
        (finiteResidue_surjective p R A E n) (finiteTransition p R A h x)).symm
    _ = _ := congrArg (finiteResidueEquiv p R A E n).symm
      (RingHom.congr_fun (finiteTransition_residue p R A E h) x)

/-- The actual p-power crystalline arrow preserves the original residue point. -/
def finiteArrow {n m : ℕ} (h : n ≤ m) :
    finiteTest p R A E P n ⟶ finiteTest p R A E P m where
  algebra := finiteTransitionAlgebra p R A E P h
  dividedPowers := P.transition h
  pointCompatible := by
    change Spec.map (CommRingCat.ofHom (residueTransition p R A E P h)) ≫
        Spec.map (CommRingCat.ofHom (finiteResidueEquiv p R A E m).symm.toRingHom) =
      Spec.map (CommRingCat.ofHom (finiteResidueEquiv p R A E n).symm.toRingHom)
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact residueTransition_point p R A E P h

/-- The original p-power test system, with every actual quotient arrow. -/
def finiteTests : ℕ ⥤ Obj p (hullPDBase p R A) (baseScheme p R A E) where
  obj := finiteTest p R A E P
  map f := finiteArrow p R A E P f.le
  map_id n := by
    apply FullPDCrystallineTests.Hom.ext
    apply AlgHom.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  map_comp f g := by
    apply FullPDCrystallineTests.Hom.ext
    apply AlgHom.ext
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl

end MathlibExt.AlgebraicGeometry.SemiperfectCrystallinePDStages
