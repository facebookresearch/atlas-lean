/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Algebra.Homology.DGCategoryTraceModels
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.SpectralObject
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

/-!
# The signed relative negative-cyclic gluing operation

Relative objects are actual cochain cones. The paper's difference is
δ_B−δ'_B, with literal fibre `sourceCompatibleComplex`. The computed
sum-cone model is identified with that source fibre by
`sourceToCompatibleIso`, negating Y and the B compatibility coefficient.
The gluing degree map keeps both exterior boundary components and lands
in CC(Z,A coproduct C), rather than discarding them into absolute CC(Z).

Every block is computed from native cone projections/inclusions, the
given cospan maps and their common B map. No freely supplied gluing
operator or nondegeneracy proof is a construction input.

Reference: Brav--Dyckerhoff, arXiv:1606.00619v1, diagram6.5 and
Theorem6.2. The v1 prose abbreviates the outer target by CC(Z); this
module retains the full relative target required by the composed cospan.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.Algebra.Homology.RelativeCyclicGluing

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open MathlibExt.CategoryTheory.DGModelContracts
open CochainComplex.HomComplex

universe u
variable {k : Type u} [CommRing k]

/-- The actual positive cone boundary is the shifted native cocycle projection. -/
def coneBoundary {A B : Cochains k} (f : A ⟶ B) : CochainComplex.mappingCone f ⟶ A⟦(1 : ℤ)⟧ :=
  Cocycle.homOf ((CochainComplex.mappingCone.fst f).rightShift 1 0 rfl)

variable {A B C X Y Z : Cochains k}

/-- The first cospan's relative cofiber retains both input complexes. -/
def relativeX (e : A ⟶ X) (f : B ⟶ X) : Cochains k :=
  CochainComplex.mappingCone (biprod.desc e f)

/-- The second cospan's relative cofiber retains its shared and exterior inputs. -/
def relativeY (g : B ⟶ Y) (h : C ⟶ Y) : Cochains k :=
  CochainComplex.mappingCone (biprod.desc g h)

/-- The X-side shared boundary has the explicit minus sign of diagram6.5. -/
def signedBoundaryX (e : A ⟶ X) (f : B ⟶ X) : relativeX e f ⟶ B⟦(1 : ℤ)⟧ :=
  -(coneBoundary (biprod.desc e f) ≫ (biprod.snd : A ⊞ B ⟶ B)⟦(1 : ℤ)⟧')

/-- The Y-side shared boundary uses the positive native cone projection. -/
def boundaryY (g : B ⟶ Y) (h : C ⟶ Y) : relativeY g h ⟶ B⟦(1 : ℤ)⟧ :=
  coneBoundary (biprod.desc g h) ≫ (biprod.fst : B ⊞ C ⟶ B)⟦(1 : ℤ)⟧'

/-- The sum-cone coefficient map is the native anti-diagonalization of the source difference. -/
def boundaryDifference (e : A ⟶ X) (f : B ⟶ X) (g : B ⟶ Y) (h : C ⟶ Y) :
    relativeX e f ⊞ relativeY g h ⟶ B⟦(1 : ℤ)⟧ :=
  biprod.desc (-signedBoundaryX e f) (boundaryY g h)

/-- The paper's literal difference δ_B−δ'_B, in the X/Y order. -/
def sourceBoundaryDifference (e : A ⟶ X) (f : B ⟶ X) (g : B ⟶ Y) (h : C ⟶ Y) :
    relativeX e f ⊞ relativeY g h ⟶ B⟦(1 : ℤ)⟧ :=
  biprod.desc (signedBoundaryX e f) (boundaryY g h)

/-- The literal compatible-class fibre in the primary source. -/
def sourceCompatibleComplex (e : A ⟶ X) (f : B ⟶ X) (g : B ⟶ Y) (h : C ⟶ Y) : Cochains k :=
  (CochainComplex.mappingCone (sourceBoundaryDifference e f g h))⟦(-1 : ℤ)⟧

/-- The sum-cone fibre used after the source's fixed native sign conversion. -/
def compatibleComplex (e : A ⟶ X) (f : B ⟶ X) (g : B ⟶ Y) (h : C ⟶ Y) : Cochains k :=
  (CochainComplex.mappingCone (boundaryDifference e f g h))⟦(-1 : ℤ)⟧

/-- The native negation automorphism of a cochain complex. -/
def negationIso (V : Cochains k) : V ≅ V where
  hom := -(𝟙 V)
  inv := -(𝟙 V)
  hom_inv_id := by simp
  inv_hom_id := by simp

/-- The source difference fibre is the computed sum-cone fibre after negating Y and B.
This is the native mapping-cone functor applied to that exact square of coefficient maps. -/
def sourceToCompatibleIso (e : A ⟶ X) (f : B ⟶ X) (g : B ⟶ Y) (h : C ⟶ Y) :
    sourceCompatibleComplex e f g h ≅ compatibleComplex e f g h := by
  let a : relativeX e f ⊞ relativeY g h ≅ relativeX e f ⊞ relativeY g h :=
    biprod.mapIso (Iso.refl _) (negationIso _)
  let b : B⟦(1 : ℤ)⟧ ≅ B⟦(1 : ℤ)⟧ := negationIso _
  have comm : sourceBoundaryDifference e f g h ≫ b.hom = a.hom ≫ boundaryDifference e f g h := by
    apply biprod.hom_ext'
    · simp [a, b, sourceBoundaryDifference, boundaryDifference, negationIso]
    · simp [a, b, sourceBoundaryDifference, boundaryDifference, negationIso]
  let q : ComposableArrows.mk₁ (sourceBoundaryDifference e f g h) ≅
      ComposableArrows.mk₁ (boundaryDifference e f g h) := ComposableArrows.isoMk₁ a b comm
  exact (shiftFunctor (Cochains k) (-1 : ℤ)).mapIso
    ((HomotopyCategory.composableArrowsFunctor (ModuleCat k)).mapIso q)

/-- Native shifted cone projection to the two input relative complexes. -/
def compatibleProjection (e : A ⟶ X) (f : B ⟶ X) (g : B ⟶ Y) (h : C ⟶ Y) :
    compatibleComplex e f g h ⟶ relativeX e f ⊞ relativeY g h :=
  (coneBoundary (boundaryDifference e f g h))⟦(-1 : ℤ)⟧' ≫
    (shiftFunctorCompIsoId (Cochains k) (1 : ℤ) (-1) (by omega)).hom.app _

/-- The actual first relative class projection keeps every cyclic coefficient. -/
def projectionX (e : A ⟶ X) (f : B ⟶ X) (g : B ⟶ Y) (h : C ⟶ Y) :
    compatibleComplex e f g h ⟶ relativeX e f := compatibleProjection e f g h ≫ biprod.fst

/-- The actual second relative class projection keeps every cyclic coefficient. -/
def projectionY (e : A ⟶ X) (f : B ⟶ X) (g : B ⟶ Y) (h : C ⟶ Y) :
    compatibleComplex e f g h ⟶ relativeY g h := compatibleProjection e f g h ≫ biprod.snd

/-- The primary difference-fibre projection uses the literal native cone boundary. -/
def sourceCompatibleProjection (e : A ⟶ X) (f : B ⟶ X) (g : B ⟶ Y) (h : C ⟶ Y) :
    sourceCompatibleComplex e f g h ⟶ relativeX e f ⊞ relativeY g h :=
  (coneBoundary (sourceBoundaryDifference e f g h))⟦(-1 : ℤ)⟧' ≫
    (shiftFunctorCompIsoId (Cochains k) (1 : ℤ) (-1) (by omega)).hom.app _

def sourceProjectionX (e : A ⟶ X) (f : B ⟶ X) (g : B ⟶ Y) (h : C ⟶ Y) :
    sourceCompatibleComplex e f g h ⟶ relativeX e f := sourceCompatibleProjection e f g h ≫ biprod.fst

def sourceProjectionY (e : A ⟶ X) (f : B ⟶ X) (g : B ⟶ Y) (h : C ⟶ Y) :
    sourceCompatibleComplex e f g h ⟶ relativeY g h := sourceCompatibleProjection e f g h ≫ biprod.snd

/-- The joint projection is the literal shifted-cone first block in every degree. -/
theorem compatibleProjection_f (e : A ⟶ X) (f : B ⟶ X) (g : B ⟶ Y) (h : C ⟶ Y) (r : ℤ) :
    (compatibleProjection e f g h).f r =
      ((CochainComplex.mappingCone (boundaryDifference e f g h)).shiftFunctorObjXIso
        (-1) r (r - 1) (by omega)).hom ≫
        (CochainComplex.mappingCone.fst (boundaryDifference e f g h)).val.v (r - 1) r (by omega) := by
  simp [compatibleProjection, coneBoundary, HomologicalComplex.comp_f,
    CochainComplex.shiftFunctor_map_f', Cocycle.homOf_f, Cocycle.rightShift_coe,
    Cochain.rightShift_v, shiftFunctorCompIsoId, CochainComplex.shiftFunctorAdd'_inv_app_f',
    CochainComplex.shiftFunctorZero_hom_app_f, CochainComplex.shiftFunctorObjXIso]
  rfl

/-- The remaining native B coefficient records the compatibility homotopy. -/
def compatibilityDegree (e : A ⟶ X) (f : B ⟶ X) (g : B ⟶ Y) (h : C ⟶ Y) (r : ℤ) :
    (compatibleComplex e f g h).X r ⟶ B.X r :=
  ((CochainComplex.mappingCone (boundaryDifference e f g h)).shiftFunctorObjXIso
      (-1) r (r - 1) (by omega)).hom ≫
    (CochainComplex.mappingCone.snd (boundaryDifference e f g h)).v (r - 1) (r - 1) (by omega) ≫
    (B.shiftFunctorObjXIso 1 (r - 1) r (by omega)).hom

/-- The composed cospan retains the actual exterior A and C cofiber. -/
def compositeRelative (e : A ⟶ X) (h : C ⟶ Y) (i : X ⟶ Z) (j : Y ⟶ Z) : Cochains k :=
  CochainComplex.mappingCone (biprod.desc (e ≫ i) (h ≫ j))

/-- The exterior A component of a compatible class is its actual first cone projection. -/
def exteriorA (e : A ⟶ X) (f : B ⟶ X) (g : B ⟶ Y) (h : C ⟶ Y) (r : ℤ) :
    (compatibleComplex e f g h).X r ⟶ A.X (r + 1) :=
  (projectionX e f g h).f r ≫ (CochainComplex.mappingCone.fst (biprod.desc e f)).val.v r (r + 1) rfl ≫
    (biprod.fst : A ⊞ B ⟶ A).f (r + 1)

/-- The exterior C component is the actual second relative cone projection. -/
def exteriorC (e : A ⟶ X) (f : B ⟶ X) (g : B ⟶ Y) (h : C ⟶ Y) (r : ℤ) :
    (compatibleComplex e f g h).X r ⟶ C.X (r + 1) :=
  (projectionY e f g h).f r ≫ (CochainComplex.mappingCone.fst (biprod.desc g h)).val.v r (r + 1) rfl ≫
    (biprod.snd : B ⊞ C ⟶ C).f (r + 1)

/-- The computed Z component includes the actual shared-boundary compatibility correction. -/
def interiorZ (e : A ⟶ X) (f : B ⟶ X) (g : B ⟶ Y) (h : C ⟶ Y)
    (i : X ⟶ Z) (j : Y ⟶ Z) (r : ℤ) : (compatibleComplex e f g h).X r ⟶ Z.X r :=
  (projectionX e f g h).f r ≫ (CochainComplex.mappingCone.snd (biprod.desc e f)).v r r (by omega) ≫ i.f r +
    (projectionY e f g h).f r ≫ (CochainComplex.mappingCone.snd (biprod.desc g h)).v r r (by omega) ≫ j.f r +
    compatibilityDegree e f g h r ≫ (f ≫ i).f r

/-- The full relative gluing degree map is fixed on every native cone block. -/
def gluingDegree (e : A ⟶ X) (f : B ⟶ X) (g : B ⟶ Y) (h : C ⟶ Y)
    (i : X ⟶ Z) (j : Y ⟶ Z) (r : ℤ) :
    (compatibleComplex e f g h).X r ⟶ (compositeRelative e h i j).X r :=
  (exteriorA e f g h r ≫ (biprod.inl : A ⟶ A ⊞ C).f (r + 1) +
      exteriorC e f g h r ≫ (biprod.inr : C ⟶ A ⊞ C).f (r + 1)) ≫
    (CochainComplex.mappingCone.inl (biprod.desc (e ≫ i) (h ≫ j))).v (r + 1) r (by omega) +
    interiorZ e f g h i j r ≫ (CochainComplex.mappingCone.inr (biprod.desc (e ≫ i) (h ≫ j))).f r

/-- The full relative gluing map retains its actual exterior A projection. -/
theorem gluingDegree_exteriorA (e : A ⟶ X) (f : B ⟶ X) (g : B ⟶ Y) (h : C ⟶ Y)
    (i : X ⟶ Z) (j : Y ⟶ Z) (r : ℤ) :
    gluingDegree e f g h i j r ≫
      (CochainComplex.mappingCone.fst (biprod.desc (e ≫ i) (h ≫ j))).val.v r (r + 1) rfl ≫
      (biprod.fst : A ⊞ C ⟶ A).f (r + 1) = exteriorA e f g h r := by
  unfold compositeRelative
  simp only [gluingDegree, Preadditive.add_comp, Category.assoc,
    CochainComplex.mappingCone.inl_v_fst_v_assoc,
    CochainComplex.mappingCone.inr_f_fst_v_assoc, zero_comp]
  simp only [← HomologicalComplex.comp_f, biprod.inl_fst, biprod.inr_fst,
    HomologicalComplex.id_f, HomologicalComplex.zero_f, Category.comp_id, comp_zero, add_zero]

/-- The full relative gluing map also retains its actual exterior C projection. -/
theorem gluingDegree_exteriorC (e : A ⟶ X) (f : B ⟶ X) (g : B ⟶ Y) (h : C ⟶ Y)
    (i : X ⟶ Z) (j : Y ⟶ Z) (r : ℤ) :
    gluingDegree e f g h i j r ≫
      (CochainComplex.mappingCone.fst (biprod.desc (e ≫ i) (h ≫ j))).val.v r (r + 1) rfl ≫
      (biprod.snd : A ⊞ C ⟶ C).f (r + 1) = exteriorC e f g h r := by
  unfold compositeRelative
  simp only [gluingDegree, Preadditive.add_comp, Category.assoc,
    CochainComplex.mappingCone.inl_v_fst_v_assoc,
    CochainComplex.mappingCone.inr_f_fst_v_assoc, zero_comp]
  simp only [← HomologicalComplex.comp_f, biprod.inl_snd, biprod.inr_snd,
    HomologicalComplex.id_f, HomologicalComplex.zero_f, Category.comp_id, comp_zero, zero_add, add_zero]

/-- The actual Z component includes the shared B compatibility coefficient. -/
theorem gluingDegree_interiorZ (e : A ⟶ X) (f : B ⟶ X) (g : B ⟶ Y) (h : C ⟶ Y)
    (i : X ⟶ Z) (j : Y ⟶ Z) (r : ℤ) :
    gluingDegree e f g h i j r ≫
      (CochainComplex.mappingCone.snd (biprod.desc (e ≫ i) (h ≫ j))).v r r (by omega) =
      interiorZ e f g h i j r := by
  unfold compositeRelative
  simp only [gluingDegree, Preadditive.add_comp, Category.assoc]
  rw [CochainComplex.mappingCone.inl_v_snd_v, CochainComplex.mappingCone.inr_f_snd_v]
  simp

/-- Assembly of the computed degree maps is the source gluing construction.
The common B square is required; the gluing map is never an independent input. -/
structure CochainGluingModel (e : A ⟶ X) (f : B ⟶ X) (g : B ⟶ Y) (h : C ⟶ Y)
    (i : X ⟶ Z) (j : Y ⟶ Z) (comm : f ≫ i = g ≫ j) where
  map : compatibleComplex e f g h ⟶ compositeRelative e h i j
  normalized : ∀ r : ℤ, map.f r = gluingDegree e f g h i j r

/-- A compatible class includes its actual negative-cyclic boundary homotopy. -/
abbrev CompatibleClass (e : A ⟶ X) (f : B ⟶ X) (g : B ⟶ Y) (h : C ⟶ Y) (n : ℤ) :=
  (𝟙_ (Cochains k))⟦n⟧ ⟶ compatibleComplex e f g h

/-- The composed class is the image under the fixed native cone-degree gluing map. -/
def gluedClass {e : A ⟶ X} {f : B ⟶ X} {g : B ⟶ Y} {h : C ⟶ Y}
    {i : X ⟶ Z} {j : Y ⟶ Z} {comm : f ≫ i = g ≫ j}
    (G : CochainGluingModel e f g h i j comm) {n : ℤ} (a : CompatibleClass e f g h n) :
    (𝟙_ (Cochains k))⟦n⟧ ⟶ compositeRelative e h i j := a ≫ G.map

end MathlibExt.Algebra.Homology.RelativeCyclicGluing
