/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.CategoryTheory.Sites.Grothendieck
public import Mathlib.RingTheory.DividedPowers.DPMorphism
public import MathlibExt.AlgebraicGeometry.GeometricPDCrystallineTests

/-!
# The full p-nilpotent affine crystalline PD basis

Objects retain the original divided-power rings, their reductions and
all scheme/algebra maps. Neither the divided-power structure nor its ideal
is required to be nilpotent. This full basis therefore permits the PD ideals of
universal A_cris/p^n thickenings. The nilpotent basis of
`GeometricPDCrystallineTests` (nilpotent divided-power structures) has a literal inclusion, with
the same actual coefficients and arrows.

References: Berthelot--Breen--Messing, Theorie de Dieudonne cristalline II;
Scholze--Weinstein1211.6357v2, Section3.2 and Proposition4.1.3.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.FullPDCrystallineTests

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- The full basis uses exactly the existing divided-power base ring. -/
abbrev PDBase := GeometricPDCrystallineTests.PDBase

variable (p : ℕ) (A : PDBase) (S : Over A.reduction)

/-- A p-nilpotent divided-power coefficient test, without any nilpotence condition on the
divided-power structure or its ideal. -/
structure Obj where
  ring : CommAlgCat.{0} A.ring
  ideal : Ideal ring
  dividedPowers : DividedPowers ideal
  baseCompatible : DividedPowers.IsDPMorphism A.dividedPowers dividedPowers
    (algebraMap A.ring ring)
  pNilpotent : IsNilpotent (p : ring)
  point : Spec (.of (ring ⧸ ideal)) ⟶ S.left
  pointBase : point ≫ S.hom = Spec.map (CommRingCat.ofHom
    (Ideal.quotientMap ideal (algebraMap A.ring ring)
      (Ideal.map_le_iff_le_comap.mp baseCompatible.ideal_comp)))

/-- The actual ambient thickening scheme. -/
abbrev Obj.thickening (P : Obj p A S) : Scheme.{0} := Spec (.of P.ring)

/-- Its actual reduction; this is not the set of reduced or geometric points. -/
abbrev Obj.reduction (P : Obj p A S) : Scheme.{0} :=
  Spec (.of (P.ring ⧸ P.ideal))

/-- The scheme-theoretic closed inclusion of the displayed divided-power ideal. -/
def Obj.inclusion (P : Obj p A S) : P.reduction ⟶ P.thickening :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk P.ideal))

variable {p A S}

/-- The real quotient map of a PD algebra map. -/
def reductionMap {P Q : Obj p A S} (f : Q.ring →ₐ[A.ring] P.ring)
    (hf : Q.ideal.map f.toRingHom ≤ P.ideal) :
    Q.ring ⧸ Q.ideal →+* P.ring ⧸ P.ideal :=
  Ideal.quotientMap P.ideal f.toRingHom (Ideal.map_le_iff_le_comap.mp hf)

/-- Crystalline arrows are precisely maps of the displayed PD diagrams. -/
@[ext] structure Hom (P Q : Obj p A S) where
  algebra : Q.ring →ₐ[A.ring] P.ring
  dividedPowers : DividedPowers.IsDPMorphism Q.dividedPowers P.dividedPowers
    algebra.toRingHom
  pointCompatible : Spec.map (CommRingCat.ofHom
    (reductionMap algebra dividedPowers.ideal_comp)) ≫ Q.point = P.point

@[simp]
theorem reductionMap_id (P : Obj p A S) :
    reductionMap (AlgHom.id A.ring P.ring)
      (DividedPowers.DPMorphism.id P.dividedPowers).ideal_comp = RingHom.id _ := by
  ext x
  simp [reductionMap]

theorem reductionMap_comp {P Q R : Obj p A S}
    (f : Q.ring →ₐ[A.ring] P.ring) (g : R.ring →ₐ[A.ring] Q.ring)
    (hf : DividedPowers.IsDPMorphism Q.dividedPowers P.dividedPowers f.toRingHom)
    (hg : DividedPowers.IsDPMorphism R.dividedPowers Q.dividedPowers g.toRingHom) :
    reductionMap (f.comp g) (hf.comp P.dividedPowers hg).ideal_comp =
      (reductionMap f hf.ideal_comp).comp (reductionMap g hg.ideal_comp) := by
  ext x
  simp [reductionMap]

instance : Category (Obj p A S) where
  Hom := Hom
  id P :=
    { algebra := AlgHom.id _ _
      dividedPowers := (DividedPowers.DPMorphism.id P.dividedPowers).isDPMorphism
      pointCompatible := by simp }
  comp f g :=
    { algebra := f.algebra.comp g.algebra
      dividedPowers := f.dividedPowers.comp _ g.dividedPowers
      pointCompatible := by
        rw [reductionMap_comp _ _ f.dividedPowers g.dividedPowers]
        change Spec.map (CommRingCat.ofHom (reductionMap g.algebra g.dividedPowers.ideal_comp) ≫
          CommRingCat.ofHom (reductionMap f.algebra f.dividedPowers.ideal_comp)) ≫ _ = _
        rw [Spec.map_comp, Category.assoc, g.pointCompatible, f.pointCompatible] }

variable (p A S)

/-- Forget only PD markings, retaining the original thickening morphisms. -/
def thickenings : Obj p A S ⥤ Scheme.{0} where
  obj P := P.thickening
  map f := Spec.map (CommRingCat.ofHom f.algebra.toRingHom)
  map_id P := Spec.map_id (.of P.ring)
  map_comp f g := Spec.map_comp (CommRingCat.ofHom g.algebra.toRingHom)
    (CommRingCat.ofHom f.algebra.toRingHom)

/-- The reduction diagram uses the original quotient algebra maps. -/
def reductions : Obj p A S ⥤ Over S.left where
  obj P := Over.mk P.point
  map f := Over.homMk (Spec.map (CommRingCat.ofHom
    (reductionMap f.algebra f.dividedPowers.ideal_comp))) f.pointCompatible
  map_id P := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (reductionMap (AlgHom.id _ _) _)) = _
    rw [reductionMap_id]
    exact Spec.map_id _
  map_comp f g := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom
      (reductionMap (f.algebra.comp g.algebra) _)) =
        Spec.map (CommRingCat.ofHom (reductionMap f.algebra _)) ≫
          Spec.map (CommRingCat.ofHom (reductionMap g.algebra _))
    rw [reductionMap_comp _ _ f.dividedPowers g.dividedPowers]
    exact Spec.map_comp (CommRingCat.ofHom (reductionMap g.algebra _))
      (CommRingCat.ofHom (reductionMap f.algebra _))

/-- An affine open cover of the actual thickening schemes. -/
def IsCover {ι : Type} (P : Obj p A S) (Q : ι → Obj p A S)
    (f : ∀ i, Q i ⟶ P) : Prop :=
  (∀ i, IsOpenImmersion ((thickenings p A S).map (f i))) ∧
    (∀ i, (Q i).ideal = P.ideal.map (f i).algebra.toRingHom) ∧
    ∀ x : P.thickening, ∃ (i : ι) (y : (Q i).thickening),
      ((thickenings p A S).map (f i)).base y = x

/-- The crystalline Zariski topology on this full affine PD basis. -/
def topology : GrothendieckTopology (Obj p A S) :=
  sInf {J | ∀ (ι : Type) (P : Obj p A S) (Q : ι → Obj p A S)
    (f : ∀ i, Q i ⟶ P), IsCover p A S P Q f → Sieve.ofArrows Q f ∈ J P}

/-- Every actual open covering family generates a covering sieve. -/
theorem cover_mem {ι : Type} (P : Obj p A S) (Q : ι → Obj p A S)
    (f : ∀ i, Q i ⟶ P) (hf : IsCover p A S P Q f) :
    Sieve.ofArrows Q f ∈ topology p A S P := by
  rw [topology, GrothendieckTopology.mem_sInf]
  intro J hJ
  exact hJ ι P Q f hf

/-- The earlier nilpotent test is viewed with the identical original PD diagram. -/
def ofNilpotent (P : GeometricPDCrystallineTests.Obj p A S) : Obj p A S :=
  { ring := P.ring, ideal := P.ideal, dividedPowers := P.dividedPowers,
    baseCompatible := P.baseCompatible, pNilpotent := P.pNilpotent,
    point := P.point, pointBase := P.pointBase }

/-- The original nilpotent basis maps to this full basis by the actual same ring maps. -/
def nilpotentInclusion : GeometricPDCrystallineTests.Obj p A S ⥤ Obj p A S where
  obj := ofNilpotent p A S
  map f :=
    { algebra := f.algebra
      dividedPowers := f.dividedPowers
      pointCompatible := f.pointCompatible }

end MathlibExt.AlgebraicGeometry.FullPDCrystallineTests
