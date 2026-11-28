/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DifferentialOperatorScalars
public import MathlibExt.AlgebraicGeometry.LocalFinitePresentation
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.Algebra.Category.ModuleCat.Stalk

/-!
# Actual right differential modules and their good filtrations

The right ring is the native sheafification of the opposite of the actual
finite-order differential-operator presheaf. Its scalar map is the native
opposite of multiplication by the actual coefficient function. Right
modules are native sheaves of modules over this fixed ring, rather than
objects equipped with an unspecified D-action.

The filtration consists of actual O-subobjects with local exhaustivity,
order-compatible right action and finite shifted local generators: near every
point, every section of `F_p` is locally a combination of the generators with
operators of order at most `p` minus their degree. Graded pieces are the
actual cokernels. This keeps Saito's right-module convention.

Source: Morihiko Saito, arXiv:1307.2140v5, sections 1.1–1.4;
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679 (Apache 2.0),
Algebra/Ring/Opposite, ModuleCat/Sheaf, ModuleCat/Stalk (Andrew Yang, 2026).
The exact ordinary differential-operator source credits remain in the
imported operator/scalar modules.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RightDifferentialModules

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite TopologicalSpace
open DifferentialOperatorSheaves DifferentialOperatorScalars
open MathlibExt.RingTheory.GeometricDifferentialOperators

def oppositeRings : RingCat.{0} ⥤ RingCat.{0} where
  obj R := RingCat.of Rᵐᵒᵖ
  map f := RingCat.ofHom (RingHom.op f.hom)
  map_id R := by ext a; rfl
  map_comp f g := by ext a; rfl

variable (k : Type) [CommRing k] (M : Type) [TopologicalSpace M]
  (O : (Opens M)ᵒᵖ ⥤ CommAlgCat.{0} k)

def rightOperatorPresheaf : (Opens M)ᵒᵖ ⥤ RingCat.{0} :=
  operatorPresheaf k M O ⋙ oppositeRings

def rightScalarFinite (U : Opens M) : O.obj (op U) →+* (finiteOperatorRing k M O U)ᵐᵒᵖ :=
  (scalarFinite k M O U).toOpposite (by
    intro a b
    change scalarFinite k M O U a * scalarFinite k M O U b =
      scalarFinite k M O U b * scalarFinite k M O U a
    rw [← map_mul, ← map_mul, mul_comm])

def rightScalarPresheafMap : coefficientPresheaf k M O ⟶ rightOperatorPresheaf k M O where
  app U := RingCat.ofHom (rightScalarFinite k M O U.unop)
  naturality {U V} f := by
    ext a
    apply MulOpposite.unop_injective
    exact congrArg (fun g ↦ g.hom a) ((scalarPresheafMap k M O).naturality f)

variable [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}]

def rightDifferentialRing : Sheaf (Opens.grothendieckTopology M) RingCat.{0} :=
  (presheafToSheaf (Opens.grothendieckTopology M) RingCat.{0}).obj
    (rightOperatorPresheaf k M O)

def rightScalarSheafMap : coefficientSheaf k M O ⟶ rightDifferentialRing k M O :=
  (presheafToSheaf (Opens.grothendieckTopology M) RingCat.{0}).map
    (rightScalarPresheafMap k M O)

abbrev RightModule := SheafOfModules.{0} (rightDifferentialRing k M O)

def underlyingO : RightModule k M O ⥤ SheafOfModules.{0} (coefficientSheaf k M O) :=
  SheafOfModules.restrictScalars (rightScalarSheafMap k M O)

def rightOperatorValue (U : Opens M) (P : finiteOperatorRing k M O U) :
    (rightDifferentialRing k M O).obj.obj (op U) :=
  ((toSheafify (Opens.grothendieckTopology M) (rightOperatorPresheaf k M O)).app (op U)).hom
    (MulOpposite.op P)

def coefficientValue (U : Opens M) (a : O.obj (op U)) :
    (coefficientSheaf k M O).obj.obj (op U) :=
  ((toSheafify (Opens.grothendieckTopology M) (coefficientPresheaf k M O)).app (op U)).hom a

theorem rightScalar_value (U : Opens M) (a : O.obj (op U)) :
    (((rightScalarSheafMap k M O).hom).app (op U)).hom (coefficientValue k M O U a) =
      rightOperatorValue k M O U (scalarFinite k M O U a) := by
  have h := toSheafify_naturality (Opens.grothendieckTopology M) (rightScalarPresheafMap k M O)
  exact (congrArg (fun g ↦ ((g.app (op U)).hom a)) h).symm

def rightAct (N : RightModule k M O) (U : Opens M)
    (P : finiteOperatorRing k M O U) (s : N.val.obj (op U)) : N.val.obj (op U) :=
  rightOperatorValue k M O U P • s

theorem rightAct_mul (N : RightModule k M O) (U : Opens M)
    (P Q : finiteOperatorRing k M O U) (s : N.val.obj (op U)) :
    rightAct k M O N U (P * Q) s = rightAct k M O N U Q (rightAct k M O N U P s) := by
  simp only [rightAct, rightOperatorValue, MulOpposite.op_mul, map_mul, mul_smul]

def OrderOn (U : Opens M) (P : finiteOperatorRing k M O U) (m : ℕ) : Prop :=
  ∀ V : Inside M U, OrderLE k (O.obj (op V.val)) m (P.val.val V)

def InFiltration (N : RightModule k M O)
    (F : ℤ → Subobject ((underlyingO k M O).obj N)) (p : ℤ) (U : Opens M)
    (s : N.val.obj (op U)) : Prop :=
  ∃ t : (Subobject.underlying.obj (F p)).val.obj (op U), ((F p).arrow.val.app (op U)).hom t = s

variable [HasSheafify (Opens.grothendieckTopology M) AddCommGrpCat.{0}]
  [(Opens.grothendieckTopology M).WEqualsLocallyBijective AddCommGrpCat.{0}]
  [∀ U : Opens M, HasWeakSheafify ((Opens.grothendieckTopology M).over U) AddCommGrpCat.{0}]
  [∀ U : Opens M,
    ((Opens.grothendieckTopology M).over U).WEqualsLocallyBijective AddCommGrpCat.{0}]

/-- A good filtration of a right differential module by coherent
`O`-submodules. -/
structure GoodFiltration where
  object : RightModule k M O
  term : ℤ → Subobject ((underlyingO k M O).obj object)
  monotone : Monotone term
  boundedBelow : ∀ x : M, ∃ U : Opens M, x ∈ U ∧ ∃ p : ℤ,
    ∀ q < p, ∀ (V : Opens M), V ≤ U → ∀ s : object.val.obj (op V),
      InFiltration k M O object term q V s → s = 0
  locallyPresented : ∀ p, LocalFinitePresentation.LocallyFinitelyPresented M
    (coefficientSheaf k M O) (Subobject.underlying.obj (term p))
  exhaustive : ∀ (U : Opens M) (s : object.val.obj (op U)) (x : U),
    ∃ (V : Opens M) (hV : V ≤ U), x.val ∈ V ∧ ∃ p : ℤ,
      InFiltration k M O object term p V ((object.val.map (homOfLE hV).op).hom s)
  orderAction : ∀ (U : Opens M) (p : ℤ) (m : ℕ) (P : finiteOperatorRing k M O U),
    OrderOn k M O U P m → ∀ s : object.val.obj (op U),
      InFiltration k M O object term p U s →
        InFiltration k M O object term (p + m) U (rightAct k M O object U P s)
  generators : ∀ x : M, ∃ U : Opens M, x ∈ U ∧
    ∃ (r : ℕ) (degree : Fin r → ℤ) (s : Fin r → object.val.obj (op U)),
      (∀ j, InFiltration k M O object term (degree j) U (s j)) ∧
      ∀ (V : Opens M) (hV : V ≤ U) (p : ℤ) (t : object.val.obj (op V)),
        InFiltration k M O object term p V t → ∀ y ∈ V,
        ∃ (W : Opens M) (hW : W ≤ V), y ∈ W ∧
        ∃ (m : Fin r → ℕ) (P : Fin r → finiteOperatorRing k M O W),
          (∀ j, P j = 0 ∨ (OrderOn k M O W (P j) (m j) ∧ degree j + m j ≤ p)) ∧
          (object.val.map (homOfLE hW).op).hom t =
            ∑ j, rightAct k M O object W (P j)
              ((object.val.map (homOfLE (hW.trans hV)).op).hom (s j))

def filtrationStep (F : GoodFiltration k M O) (p : ℤ) :
    Subobject.underlying.obj (F.term (p - 1)) ⟶ Subobject.underlying.obj (F.term p) :=
  Subobject.underlying.map (homOfLE (F.monotone (by omega)))

def gradedPiece (F : GoodFiltration k M O) (p : ℤ) :
    SheafOfModules.{0} (coefficientSheaf k M O) := cokernel (filtrationStep k M O F p)

end MathlibExt.AlgebraicGeometry.RightDifferentialModules
