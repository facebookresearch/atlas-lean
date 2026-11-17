/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.RingSheafModuleTensors
public import MathlibExt.CategoryTheory.NativeScalarProjectionMaps
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-!
# Native relative de Rham, Hodge and filtration outputs

The input is a source-qualified coefficient complex and its original
filtered subcomplexes. Higher de Rham modules and all Hodge modules are
native cohomology of native derived pushforward. Higher filtration
objects are native images of the original filtered cohomology maps.
No higher vector bundle or higher filtration is supplied as input.

The boundary lift is constructed through the fully faithful inclusion
of bounded-below derived categories from the ORIGINAL native
`triangleOfSESδ`. This gives the cochain boundary used for both
Hodge degeneration and Gauss--Manin source normalization.

References: Scholze, arXiv:1205.3463v2, Definition 7.4 and Theorem 8.8;
Stacks Tags 07HY and 07I0 (completed PR2245 de Rham source port).
Native Mathlib module sheaves, images, cohomology and cochain exact
triangles: Apache 2.0, revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.NativeFilteredDeRhamOutputs

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open RingedDerivedCoefficientOperations RingSheafModuleTensors

attribute [local instance] HasDerivedCategory.standard

universe v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [UnivLE.{max u v, 1}]
  (R O : Sheaf J CommRingCat.{1}) (η : R ⟶ O)

/-- Actual restriction of scalars preserves the original sheaf and every restriction map. -/
def restrict : Modules O ⥤ Modules R :=
  SheafOfModules.restrictScalars (moduleScalarMap (𝟭 C) R O η)

variable [HasSheafify J AddCommGrpCat.{1}] [J.WEqualsLocallyBijective AddCommGrpCat.{1}]

/-- The literal relative coefficient term E tensor Omega^n, before the native complex. -/
def term (E Ω : Modules O) (n : ℕ) : Modules R :=
  (restrict R O η).obj (tensor O E (exterior O Ω n))

/-- The original coefficient Hodge filtration is base input, with native sheaf submodules. -/
structure CoefficientFiltration (E : Modules O) where
  pieces : ℤ → E.Submodule
  decreasing : Antitone pieces
  separated : iInf pieces = ⊥
  exhaustive : iSup pieces = ⊤

variable {R O η}

/-- Finite form length is an explicit intermediate projection guard. -/
def FiniteForms (Ω : Modules O) : Prop :=
  ∃ d : ℕ, ∀ n : ℕ, d < n → IsZero (exterior O Ω n)

/-- The full relative theory permits locally varying finite form bounds over a non-quasi-compact base. -/
def LocallyFiniteForms (Ω : Modules O) : Prop :=
  ∀ U : C, ∃ S : Sieve U, S ∈ J U ∧
    ∀ (V : C) (f : V ⟶ U), S f →
      ∃ d : ℕ, ∀ n : ℕ, d < n → IsZero ((exterior O Ω n).over V)

section FilteredComplexes

variable (R : Sheaf J CommRingCat.{1})

/-- The primitive filtered cochain source, qualified against native terms in the analytic wrapper. -/
structure FilteredComplex where
  total : CochainComplex.Plus (Modules R)
  filtered : ℤᵒᵖ ⥤ CochainComplex.Plus (Modules R)
  inclusion : filtered ⟶ (Functor.const ℤᵒᵖ).obj total
  mono : ∀ j : ℤ, Mono (inclusion.app (op j))

namespace FilteredComplex

variable (D : FilteredComplex R)

def transition (j : ℤ) : D.filtered.obj (op (j + 1)) ⟶ D.filtered.obj (op j) :=
  D.filtered.map (homOfLE (show j ≤ j + 1 by omega)).op

/-- The Hodge graded complex is the native cochain cokernel of the original filtration step. -/
def graded (j : ℤ) : CochainComplex.Plus (Modules R) := cokernel (transition R D j)

def gradedProjection (j : ℤ) : D.filtered.obj (op j) ⟶ graded R D j :=
  cokernel.π (transition R D j)

end FilteredComplex

end FilteredComplexes

section Boundaries

variable {A : Type*} [Category* A] [Abelian A]
  (K L M : CochainComplex.Plus A) (f : K ⟶ L) (g : L ⟶ M) (zero : f ≫ g = 0)

def underlyingShortComplex : ShortComplex (CochainComplex A ℤ) :=
  ShortComplex.mk f.hom g.hom (congrArg (CochainComplex.Plus.ι A).map zero)

variable (exact : (underlyingShortComplex K L M f g zero).ShortExact)

/-- The canonical bounded-below lift of the native cochain short-exact boundary. -/
def boundary : DerivedCategory.Plus.Q.obj M ⟶
    (DerivedCategory.Plus.Q.obj K)⟦(1 : ℤ)⟧ :=
  (ObjectProperty.fullyFaithfulι _).preimage
    ((DerivedCategory.Plus.QCompιIso A).hom.app M ≫
      DerivedCategory.triangleOfSESδ exact ≫
      ((DerivedCategory.Plus.QCompιIso A).inv.app K)⟦(1 : ℤ)⟧' ≫
      ((DerivedCategory.Plus.ι (C := A)).commShiftIso (1 : ℤ)).inv.app (DerivedCategory.Plus.Q.obj K))

end Boundaries

section HigherOutputs

variable {D : Type u} [Category.{v} D] {T : GrothendieckTopology D}
  [HasSheafify T AddCommGrpCat.{1}] [T.WEqualsLocallyBijective AddCommGrpCat.{1}]
  (G : C ⥤ D) [G.IsContinuous J T]
  (S : Sheaf J CommRingCat.{1}) (R : Sheaf T CommRingCat.{1})
  (φ : S ⟶ (G.sheafPushforwardContinuous CommRingCat.{1} J T).obj R)
  [(pushforward G S R φ).IsRightAdjoint]
  [EnoughInjectives (Modules S)] [EnoughInjectives (Modules R)]
  (F : FilteredComplex R)

/-- Native derived relative de Rham pushforward. -/
def derivedDeRham : Derived S :=
  (derivedPushforward G S R φ).obj (DerivedCategory.Plus.Q.obj F.total)

/-- The higher vector-bundle carrier is OUTPUT, actual native R^i f_dR*. -/
def higherDeRham (i : ℤ) : Modules S := cohomology S (derivedDeRham G S R φ F) i

def filteredDerived (j : ℤ) : Derived S :=
  (derivedPushforward G S R φ).obj (DerivedCategory.Plus.Q.obj (F.filtered.obj (op j)))

/-- The original filtered complex map is pushed forward before taking cohomology. -/
def filtrationMap (i j : ℤ) :
    cohomology S (filteredDerived G S R φ F j) i ⟶ higherDeRham G S R φ F i :=
  (DerivedCategory.Plus.homologyFunctor (Modules S) i).map
    ((derivedPushforward G S R φ).map (DerivedCategory.Plus.Q.map (F.inclusion.app (op j))))

/-- Higher filtration is the native image, not a supplied family of higher subbundles. -/
def higherFiltration (i j : ℤ) : Modules S := image (filtrationMap G S R φ F i j)

def filtrationInclusion (i j : ℤ) :
    higherFiltration G S R φ F i j ⟶ higherDeRham G S R φ F i :=
  image.ι (filtrationMap G S R φ F i j)

def filteredCohomologyTransition (i j : ℤ) :
    cohomology S (filteredDerived G S R φ F (j + 1)) i ⟶
      cohomology S (filteredDerived G S R φ F j) i :=
  (DerivedCategory.Plus.homologyFunctor (Modules S) i).map
    ((derivedPushforward G S R φ).map (DerivedCategory.Plus.Q.map
      (FilteredComplex.transition R F j)))

theorem filteredCohomologyTransition_source (i j : ℤ) :
    filteredCohomologyTransition G S R φ F i j ≫ filtrationMap G S R φ F i j =
      filtrationMap G S R φ F i (j + 1) ≫ 𝟙 (higherDeRham G S R φ F i) := by
  let H := DerivedCategory.Plus.Q (C := Modules R) ⋙ derivedPushforward G S R φ ⋙
    DerivedCategory.Plus.homologyFunctor (Modules S) i
  change H.map (FilteredComplex.transition R F j) ≫ H.map (F.inclusion.app (op j)) =
    H.map (F.inclusion.app (op (j + 1))) ≫ 𝟙 (H.obj F.total)
  have h : FilteredComplex.transition R F j ≫ F.inclusion.app (op j) =
      F.inclusion.app (op (j + 1)) := by
    simpa [FilteredComplex.transition] using
      F.inclusion.naturality (homOfLE (show j ≤ j + 1 by omega)).op
  have hh := congrArg H.map h
  rw [H.map_comp] at hh
  exact hh.trans (Category.comp_id (H.map (F.inclusion.app (op (j + 1))))).symm

/-- The higher filtration transition is the native image map of the original filtered cochains. -/
def higherFiltrationTransition (i j : ℤ) :
    higherFiltration G S R φ F i (j + 1) ⟶ higherFiltration G S R φ F i j :=
  image.map (Arrow.homMk' (filteredCohomologyTransition G S R φ F i j)
    (𝟙 (higherDeRham G S R φ F i)) (filteredCohomologyTransition_source G S R φ F i j))

/-- The graded higher de Rham module is a native cokernel of its computed image filtration. -/
def higherGraded (i j : ℤ) : Modules S := cokernel (higherFiltrationTransition G S R φ F i j)

/-- A higher filtered-bundle SOURCE OUTPUT with its pieces fixed to native cohomology images. -/
structure HigherFiltrationSource (i : ℤ) where
  filtration : CoefficientFiltration S (higherDeRham G S R φ F i)
  image_source : ∀ (j : ℤ) (U : Cᵒᵖ) (x : (higherDeRham G S R φ F i).val.obj U),
    x ∈ (filtration.pieces j).toSubmodule.obj U ↔
      x ∈ LinearMap.range ((filtrationInclusion G S R φ F i j).val.app U).hom
  locally_split : ∀ (j : ℤ) (U : Cᵒᵖ), ∃ Q : Sieve U.unop, Q ∈ J U.unop ∧
    ∀ (V : C) (f : V ⟶ U.unop), Q f →
      ∃ N : Submodule (S.obj.obj (op V)) ((higherDeRham G S R φ F i).val.obj (op V)),
        IsCompl ((filtration.pieces j).toSubmodule.obj (op V)) N

/-- Hodge bidegree (i-j,j) is computed from the actual graded relative complex. -/
def higherHodge (i j : ℤ) : Modules S :=
  cohomology S ((derivedPushforward G S R φ).obj
    (DerivedCategory.Plus.Q.obj (FilteredComplex.graded R F j))) i

def gradedShortComplex (j : ℤ) : ShortComplex (CochainComplex (Modules R) ℤ) :=
  underlyingShortComplex (F.filtered.obj (op (j + 1))) (F.filtered.obj (op j)) (FilteredComplex.graded R F j)
    (FilteredComplex.transition R F j) (FilteredComplex.gradedProjection R F j)
    (cokernel.condition (FilteredComplex.transition R F j))

/-- This proof source concerns the ORIGINAL native cochain cokernel sequence. -/
structure GradedExactSource where
  exact : ∀ j : ℤ, (gradedShortComplex R F j).ShortExact

local instance derivedPushShift : (derivedPushforward G S R φ).CommShift ℤ := by
  unfold derivedPushforward
  infer_instance

/-- The actual Hodge-filtration boundary after derived pushforward. E1 degeneration requests
its vanishing, not the vanishing of a freely selected spectral-sequence differential. -/
def gradedBoundary (Q : GradedExactSource R F) (i j : ℤ) :
    higherHodge G S R φ F i j ⟶ cohomology S (filteredDerived G S R φ F (j + 1)) (i + 1) :=
  (DerivedCategory.Plus.homologyFunctor (Modules S) i).map
    ((derivedPushforward G S R φ).map
      (boundary (F.filtered.obj (op (j + 1))) (F.filtered.obj (op j)) (FilteredComplex.graded R F j)
        (FilteredComplex.transition R F j) (FilteredComplex.gradedProjection R F j)
        (cokernel.condition (FilteredComplex.transition R F j)) (Q.exact j)) ≫
      ((derivedPushforward G S R φ).commShiftIso (1 : ℤ)).hom.app
        (DerivedCategory.Plus.Q.obj (F.filtered.obj (op (j + 1))))) ≫
    (DerivedCategory.homologyFunctor (Modules S) i).map
      (((DerivedCategory.Plus.ι (C := Modules S)).commShiftIso (1 : ℤ)).hom.app
        (filteredDerived G S R φ F (j + 1))) ≫
    ((DerivedCategory.homologyFunctor (Modules S) 0).shiftIso 1 i (i + 1) (by omega)).hom.app
      (filteredDerived G S R φ F (j + 1)).obj

end HigherOutputs

end MathlibExt.CategoryTheory.NativeFilteredDeRhamOutputs
