/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# Li's actual Cech differential and obstruction complex

D is the literal alternating coface complex. From the actual curve
extension map delta, the total terms are F0, F1 plus D0, D1, D2, ... .
The displayed differentials are (d,-delta0), (delta1,partial), partial.
The signs and both compatibility equations are retained before homology
or finite-free replacement. Geometric dictionaries must identify the
cosimplicial values and delta with log derivations and differences of the
actual lifted maps; a name or a numerical virtual rank does not do that.
Source: Jun Li arXiv:math/0110113v1, equations1.18--1.20, printed pp15--16,
and equations1.23--1.25, printed pp21--22.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.LiCechObstructionComplexes

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology
open scoped Simplicial

variable (A : Type) [CommRing A]

structure Data where
  zero : ModuleCat.{0} A
  one : ModuleCat.{0} A
  sourceDifferential : zero ⟶ one
  logCochains : CosimplicialObject (ModuleCat.{0} A)
  deltaZero : zero ⟶ logCochains.obj ⦋0⦌
  deltaOne : one ⟶ logCochains.obj ⦋1⦌
  compatibility : sourceDifferential ≫ deltaOne =
    deltaZero ≫ AlternatingCofaceMapComplex.objD logCochains 0
  cocycle : deltaOne ≫ AlternatingCofaceMapComplex.objD logCochains 1 = 0

variable {A}

def logComplex (L : Data A) : CochainComplex (ModuleCat.{0} A) ℕ :=
  (alternatingCofaceMapComplex _).obj L.logCochains

def term (L : Data A) : ℕ → ModuleCat.{0} A
  | 0 => L.zero
  | 1 => ModuleCat.of A (L.one × L.logCochains.obj ⦋0⦌)
  | n + 2 => L.logCochains.obj ⦋n + 1⦌

def firstStep (L : Data A) : term L 0 ⟶ term L 1 :=
  ModuleCat.ofHom (L.sourceDifferential.hom.prod (-L.deltaZero.hom))

def secondStep (L : Data A) : term L 1 ⟶ term L 2 :=
  ModuleCat.ofHom
    (L.deltaOne.hom.coprod (AlternatingCofaceMapComplex.objD L.logCochains 0).hom)

def step (L : Data A) : ∀ n : ℕ, term L n ⟶ term L (n + 1)
  | 0 => firstStep L
  | 1 => secondStep L
  | n + 2 => AlternatingCofaceMapComplex.objD L.logCochains (n + 1)

theorem first_second (L : Data A) : firstStep L ≫ secondStep L = 0 := by
  apply ModuleCat.hom_ext
  ext x
  change L.deltaOne (L.sourceDifferential x) +
    (AlternatingCofaceMapComplex.objD L.logCochains 0) (-L.deltaZero x) = 0
  have h := ConcreteCategory.congr_hom L.compatibility x
  change L.deltaOne (L.sourceDifferential x) =
    (AlternatingCofaceMapComplex.objD L.logCochains 0) (L.deltaZero x) at h
  rw [h, map_neg, add_neg_cancel]

theorem second_third (L : Data A) : secondStep L ≫ step L 2 = 0 := by
  apply ModuleCat.hom_ext
  ext x
  change (AlternatingCofaceMapComplex.objD L.logCochains 1)
    (L.deltaOne x.1 + (AlternatingCofaceMapComplex.objD L.logCochains 0) x.2) = 0
  rw [map_add]
  have h := ConcreteCategory.congr_hom L.cocycle x.1
  have h' := ConcreteCategory.congr_hom
    (AlternatingCofaceMapComplex.d_squared L.logCochains 0) x.2
  change (AlternatingCofaceMapComplex.objD L.logCochains 1) (L.deltaOne x.1) = 0 at h
  change (AlternatingCofaceMapComplex.objD L.logCochains 1)
    ((AlternatingCofaceMapComplex.objD L.logCochains 0) x.2) = 0 at h'
  rw [h, h', zero_add]

def complex (L : Data A) : CochainComplex (ModuleCat.{0} A) ℕ :=
  CochainComplex.of (term L) (step L) (by
    intro n
    match n with
    | 0 => exact first_second L
    | 1 => exact second_third L
    | n + 2 => exact AlternatingCofaceMapComplex.d_squared L.logCochains (n + 1))

def integerComplex (L : Data A) : CochainComplex (ModuleCat.{0} A) ℤ :=
  (complex L).extend (ComplexShape.embeddingUpIntGE 0)

def degreeOneIso (L : Data A) : (integerComplex L).X (1 : ℤ) ≅ term L 1 :=
  (complex L).extendXIso (ComplexShape.embeddingUpIntGE 0) (i := (1 : ℕ)) (by simp)

def degreeTwoIso (L : Data A) : (integerComplex L).X (2 : ℤ) ≅ L.logCochains.obj ⦋1⦌ :=
  (complex L).extendXIso (ComplexShape.embeddingUpIntGE 0) (i := (2 : ℕ)) (by simp)

@[simp] theorem firstStep_value (L : Data A) (x : L.zero) :
    firstStep L x = (L.sourceDifferential x, -L.deltaZero x) := rfl

@[simp] theorem secondStep_value (L : Data A) (x : L.one × L.logCochains.obj ⦋0⦌) :
    secondStep L x = L.deltaOne x.1 + (AlternatingCofaceMapComplex.objD L.logCochains 0) x.2 := rfl

end MathlibExt.AlgebraicGeometry.LiCechObstructionComplexes
