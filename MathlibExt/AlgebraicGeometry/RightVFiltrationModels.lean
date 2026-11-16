/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RightCoordinateDifferentials
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits

/-!
# Actual rational V pieces and right nearby/vanishing operators

V pieces are native subsheaves of the original right module restricted
to O. The filtration decreases in alpha; t raises alpha and partial
lowers it. The V-zero operators preserve every actual coordinate ideal.
The graded piece is the native sheaf cokernel of V^(>alpha) into V^alpha.
Graded operators are characterized on all original section lifts by
the original finite-order operators. Their construction remains a
separate source request. Nearby-unipotent and vanishing carriers are
grV^0 and grV^-1, with can=partial and var=t.

V is unrestricted on the t-invertible locus, where all its pieces may
equal the original module. The ungraded partial action is coefficient
linear. On grV^a to grV^(a-1), its coefficient commutator lies in V^a
and vanishes modulo V^(>a-1). The Euler commutator lies in t V^a,
hence in V^(a+1), and vanishes modulo V^(>a). This gives the graded
O-linear maps used below.

Source: Saito1307.2140v5, Sections2.1,2.2 and2.4. Nilpotence uses the
source right Euler operator partial*t+alpha. Native subsheaf lattices
and cokernels are Mathlib56a005855ea17e0b0958f73ec801ae140b0a1679,
Apache2.0, Christian Merten, Joël Riou and the Mathlib contributors.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RightVFiltrationModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite TopologicalSpace
open DifferentialOperatorSheaves RightDifferentialModules RightCoordinateDifferentials

variable (k : Type) [CommRing k] [Algebra ℚ k] (M : Type) [TopologicalSpace M]
  (O : (Opens M)ᵒᵖ ⥤ CommAlgCat.{0} k)
  [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}]
  (C : CoordinateDerivation k M O) (N : RightModule k M O)

/-- Actual V-zero operators preserve every power of the coordinate ideal on every subopen. -/
def VOrderZero (U : Opens M) (P : finiteOperatorRing k M O U) : Prop :=
  ∀ (V : Inside M U) (r : ℕ) (a : O.obj (op V.val)),
    ∃ b : O.obj (op V.val), P.val.val V (C.function V.val ^ r * a) = C.function V.val ^ r * b

/-- A decreasing rational filtration on the actual O-subsheaves of the right module. -/
structure RationalVFiltration where
  term : ℚ → ((underlyingO k M O).obj N).Submodule
  decreasing : Antitone term
  leftContinuous : ∀ a : ℚ, term a = ⨅ b : {b : ℚ // b < a}, term b.val
  locallyDiscrete : ∀ x : M, ∃ U : Opens M, x ∈ U ∧ ∃ e : ℕ, 0 < e ∧
    ∀ (W : Opens M), W ≤ U → ∀ (n : ℤ) (a b : ℚ),
      (n : ℚ) < e * a → e * a ≤ (n : ℚ) + 1 →
      (n : ℚ) < e * b → e * b ≤ (n : ℚ) + 1 →
      (term a).toSubmodule.obj (op W) = (term b).toSubmodule.obj (op W)
  exhaustive : ∀ (U : Opens M) (s : N.val.obj (op U)) (x : U),
    ∃ (V : Opens M) (hV : V ≤ U), x.val ∈ V ∧ ∃ a : ℚ,
      (N.val.map (homOfLE hV).op).hom s ∈ (term a).toSubmodule.obj (op V)
  coordinateAction : ∀ (a : ℚ) (U : Opens M) (s : N.val.obj (op U)),
    s ∈ (term a).toSubmodule.obj (op U) →
      rightCoordinate k M O C N U s ∈ (term (a + 1)).toSubmodule.obj (op U)
  partialAction : ∀ (a : ℚ) (U : Opens M) (s : N.val.obj (op U)),
    s ∈ (term a).toSubmodule.obj (op U) →
      rightPartial k M O C N U s ∈ (term (a - 1)).toSubmodule.obj (op U)
  zeroOrderAction : ∀ (a : ℚ) (U : Opens M) (P : finiteOperatorRing k M O U),
    VOrderZero k M O C U P → ∀ s : N.val.obj (op U),
      s ∈ (term a).toSubmodule.obj (op U) →
        rightAct k M O N U P s ∈ (term a).toSubmodule.obj (op U)
  localGenerators : ∀ (a : ℚ) (x : M), ∃ U : Opens M, x ∈ U ∧
    ∃ (r : ℕ) (s : Fin r → N.val.obj (op U)),
      (∀ j, s j ∈ (term a).toSubmodule.obj (op U)) ∧
      ∀ (V : Opens M) (hV : V ≤ U) (t : N.val.obj (op V)),
        t ∈ (term a).toSubmodule.obj (op V) →
        ∃ P : Fin r → finiteOperatorRing k M O V,
          (∀ j, VOrderZero k M O C V (P j)) ∧
          t = ∑ j, rightAct k M O N V (P j) ((N.val.map (homOfLE hV).op).hom (s j))
  eulerNilpotent : ∀ (a : ℚ) (x : M), ∃ U : Opens M, x ∈ U ∧ ∃ r : ℕ, 0 < r ∧
    ∀ (V : Opens M), V ≤ U → ∀ s : N.val.obj (op V),
      s ∈ (term a).toSubmodule.obj (op V) →
      ((rightEuler k M O C N V (algebraMap ℚ k a))^[r]) s ∈
        (⨆ b : {b : ℚ // a < b}, term b.val).toSubmodule.obj (op V)

variable (V : RationalVFiltration k M O C N)

/-- The actual positive-index union, formed in the native subsheaf lattice. -/
def termAbove (a : ℚ) : ((underlyingO k M O).obj N).Submodule :=
  ⨆ b : {b : ℚ // a < b}, V.term b.val

/-- The decreasing filtration includes the entire positive-index union in its alpha piece. -/
theorem termAbove_le (a : ℚ) : termAbove k M O C N V a ≤ V.term a := by
  apply iSup_le
  intro b
  exact V.decreasing b.property.le

/-- Native inclusion of two actual sheaf submodules. -/
def subsheafInclusion {A B : ((underlyingO k M O).obj N).Submodule} (h : A ≤ B) :
    A.toSheafOfModules ⟶ B.toSheafOfModules :=
  ⟨PresheafOfModules.Submodule.homOfLE (SheafOfModules.Submodule.le_iff.mp h)⟩

/-- The actual map V^(>alpha) into V^alpha, retaining the original module restriction maps. -/
def vStep (a : ℚ) :
    (termAbove k M O C N V a).toSheafOfModules ⟶ (V.term a).toSheafOfModules :=
  subsheafInclusion k M O N (termAbove_le k M O C N V a)

variable [HasSheafify (Opens.grothendieckTopology M) AddCommGrpCat.{0}]
  [(Opens.grothendieckTopology M).WEqualsLocallyBijective AddCommGrpCat.{0}]
  [∀ U : Opens M, HasWeakSheafify ((Opens.grothendieckTopology M).over U) AddCommGrpCat.{0}]
  [∀ U : Opens M, ((Opens.grothendieckTopology M).over U).WEqualsLocallyBijective AddCommGrpCat.{0}]

/-- The actual V-graded O-module is the native cokernel of the positive-index inclusion. -/
def gradedV (a : ℚ) : SheafOfModules.{0} (DifferentialOperatorScalars.coefficientSheaf k M O) :=
  cokernel (vStep k M O C N V a)

/-- The original alpha-piece quotient map. -/
def gradedProjection (a : ℚ) : (V.term a).toSheafOfModules ⟶ gradedV k M O C N V a :=
  cokernel.π (vStep k M O C N V a)

/-- Graded operators are fixed on all original section lifts by actual t, partial and right Euler. -/
structure GradedVOperators where
  partialMap : ∀ a : ℚ, gradedV k M O C N V a ⟶ gradedV k M O C N V (a - 1)
  coordinateMap : ∀ a : ℚ, gradedV k M O C N V a ⟶ gradedV k M O C N V (a + 1)
  eulerMap : ∀ a : ℚ, End (gradedV k M O C N V a)
  partial_normal : ∀ (a : ℚ) (U : Opens M)
      (s : (V.term a).toSheafOfModules.val.obj (op U))
      (t : (V.term (a - 1)).toSheafOfModules.val.obj (op U)),
    ((V.term (a - 1)).ι.val.app (op U)).hom t =
      rightPartial k M O C N U (((V.term a).ι.val.app (op U)).hom s) →
    ((partialMap a).val.app (op U)).hom (((gradedProjection k M O C N V a).val.app (op U)).hom s) =
      ((gradedProjection k M O C N V (a - 1)).val.app (op U)).hom t
  coordinate_normal : ∀ (a : ℚ) (U : Opens M)
      (s : (V.term a).toSheafOfModules.val.obj (op U))
      (t : (V.term (a + 1)).toSheafOfModules.val.obj (op U)),
    ((V.term (a + 1)).ι.val.app (op U)).hom t =
      rightCoordinate k M O C N U (((V.term a).ι.val.app (op U)).hom s) →
    ((coordinateMap a).val.app (op U)).hom (((gradedProjection k M O C N V a).val.app (op U)).hom s) =
      ((gradedProjection k M O C N V (a + 1)).val.app (op U)).hom t
  euler_normal : ∀ (a : ℚ) (U : Opens M)
      (s t : (V.term a).toSheafOfModules.val.obj (op U)),
    ((V.term a).ι.val.app (op U)).hom t =
      rightEuler k M O C N U (algebraMap ℚ k a) (((V.term a).ι.val.app (op U)).hom s) →
    ((eulerMap a).asHom.val.app (op U)).hom
        (((gradedProjection k M O C N V a).val.app (op U)).hom s) =
      ((gradedProjection k M O C N V a).val.app (op U)).hom t

/-- Saito's actual nearby-unipotent underlying O-module. -/
abbrev nearbyUnipotent := gradedV k M O C N V 0

/-- Saito's actual vanishing-unipotent underlying O-module. -/
abbrev vanishingUnipotent := gradedV k M O C N V (-1)

/-- The canonical can operator is the original partial derivative on grV^0. -/
def can (A : GradedVOperators k M O C N V) :
    nearbyUnipotent k M O C N V ⟶ vanishingUnipotent k M O C N V := by
  simpa using A.partialMap 0

/-- The canonical var operator is original multiplication by t on grV^-1. -/
def var (A : GradedVOperators k M O C N V) :
    vanishingUnipotent k M O C N V ⟶ nearbyUnipotent k M O C N V := by
  simpa using A.coordinateMap (-1)

/-- Nearby monodromy retains the actual can followed by var, before the Tate target twist. -/
def nearbyMonodromy (A : GradedVOperators k M O C N V) :
    End (nearbyUnipotent k M O C N V) :=
  ⟨can k M O C N V A ≫ var k M O C N V A⟩

/-- Vanishing monodromy retains the actual var followed by can. -/
def vanishingMonodromy (A : GradedVOperators k M O C N V) :
    End (vanishingUnipotent k M O C N V) :=
  ⟨var k M O C N V A ≫ can k M O C N V A⟩

end MathlibExt.AlgebraicGeometry.RightVFiltrationModels
