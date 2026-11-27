/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.CategoryTheory.DGRelativeCYCospanGluing
public import WantedExt.AlgebraicGeometry.DGInductionDiagramFoundationsWanted
public import WantedExt.AlgebraicGeometry.RelativeCalabiYauFoundationsWanted

/-!
# Wanted normalized relative CY cospan integration and composition

The class-independent source 6.1 construction is the actual total-cofiber
quasi-isomorphism of bar counits. Its dual is fixed by representable Hom
precomposition. The whole cospan integration retains the actual categories,
all bar/dual data, unit mates, coproduct signs, every coherent index cell,
and one projectively cofibrant joint comparison for each compatible class.

The final nondegeneracy theorem assumes only that the two actual
projections define relative CY structures. Its conclusion concerns the
computed full relative A/C gluing class. No absolute boundary CY assertion
or output nondegeneracy callback is a construction input.

Reference: Brav--Dyckerhoff, arXiv:1606.00619v1, Theorems 6.1 and 6.2,
Definition 4.11 and diagrams 6.5--6.7. The ground ring is a field; this
composition theorem has no characteristic-zero restriction.
-/

namespace WantedExt.AlgebraicGeometry.DGRelativeCYDiagramLedgerWanted

open CategoryTheory
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels
open MathlibExt.CategoryTheory.DGModuleConeShiftModels
open MathlibExt.CategoryTheory.DGModuleUniversalConeModels
open MathlibExt.CategoryTheory.DGRelativeCalabiYauModels
open MathlibExt.CategoryTheory.DGRelativeCYDiagramLedger
open MathlibExt.CategoryTheory.DGRelativeCYCospanGluing
open MathlibExt.CategoryTheory.DGMoritaCospanModels
open MathlibExt.CategoryTheory.DGCoherentIndexModels
open MathlibExt.CategoryTheory.CosimplicialDGMappingModels
open MathlibExt.Algebra.Homology.DGCategoryTraceModels

universe u

/-- The bar-counit square commutes by the fixed native induction units and actual bar maps. -/
theorem_wanted relative_cy_bar_counit_square (k : Type u) [Field k] (P : Cospan (k := k))
    (S : NegativeTraceSystem k) (n : ℤ) (D : ModuleData P S n) (K : InductionData D) :
  BarCounitSquare D K

/-- Source Theorem 6.1: the single computed total bar-counit cofiber compares quasi-isomorphically to Z. -/
def_wanted dg_morita_bar_counit_pushout (k : Type u) [Field k] (R : DGFrameSystem k)
    (P : Cospan (k := k)) (S : NegativeTraceSystem k) (n : ℤ)
    (D : ModuleData P S n) (K : InductionData D) (B : BarCounitSquare D K)
    (pushout : IsMoritaPushout R P.f P.g P.i P.j P.square) : ModuleHomotopyPushout B.square

/-- The one source 6.1 comparison is dualized by its actual representable Hom precomposition. -/
def_wanted dg_morita_bar_counit_pushout_dual (k : Type u) [Field k]
    (P : Cospan (k := k)) (S : NegativeTraceSystem k) (n : ℤ)
    (D : ModuleData P S n) (K : InductionData D) (B : BarCounitSquare D K)
    (Q : ModuleHomotopyPushout B.square) : DualCotangentComparison B Q

/-- The square's degree -1 cell is the signed difference of its two native chain cells. -/
theorem_wanted dg_coherent_grid_square (k : Type u) [Field k]
    (R : CoherentIndexModel k GridIndex) (C : DGCat k) (Q : CoherentDiagram R C)
    (nodes : GridIndex → DGDerivedModules k C)
    (eq : ∀ q : GridIndex, Q.toEnrichedFunctor.obj (R.objects.symm q) = (nodes q).obj)
    (s : SmallSquare) : CoherentSquareModel Q nodes eq s

/-- The coproduct diagonal split uses actual bar inclusions and the fixed composition units. -/
def_wanted relative_cy_coproduct_split_context (k : Type u) [Field k] (A B X : DGCat k)
    (S : NegativeTraceSystem k) (P : DGCoproductModel A B) (f : A ⟶ X) (g : B ⟶ X)
    (U : CoproductFunctorModel P f g) (DA : CYCategoryData S A) (DB : CYCategoryData S B)
    (DP : CYCategoryData S P.category) (DX : CYCategoryData S X)
    (E : RelativeCYContext S f DA DX) (F : RelativeCYContext S g DB DX)
    (EF : RelativeCYContext S U.functor DP DX) : CoproductSplitContext P f g U DA DB DP DX E F EF

/-- The four coproduct-square arrows are normalized by native shifts and signed cone blocks. -/
def_wanted relative_cy_coproduct_square_operators (k : Type u) [Field k] (A B X : DGCat k)
    (S : NegativeTraceSystem k) (P : DGCoproductModel A B) (f : A ⟶ X) (g : B ⟶ X)
    (U : CoproductFunctorModel P f g) (DA : CYCategoryData S A) (DB : CYCategoryData S B)
    (DP : CYCategoryData S P.category) (DX : CYCategoryData S X)
    (E : RelativeCYContext S f DA DX) (F : RelativeCYContext S g DB DX)
    (EF : RelativeCYContext S U.functor DP DX) (K : CoproductSplitContext P f g U DA DB DP DX E F EF)
    (n : ℤ) (C : RelativeConeContext EF n)
    (SA : CofibrantShiftModel (⟨DA.bar.module, DA.bar.cofibrant⟩) (1 - n))
    (SB : CofibrantShiftModel (⟨DB.bar.module, DB.bar.cofibrant⟩) (1 - n)) :
  CoproductSquareOperators K n C SA SB

/-- The normalized cyclic coproduct maps and signed full relative cone gluing are actual constructions. -/
def_wanted relative_cy_cospan_cyclic_data (k : Type u) [Field k] (P : Cospan (k := k))
    (S : NegativeTraceSystem k) (n : ℤ) (D : ModuleData P S n) : CyclicData D

/-- Class-induced matrices and signed boundary maps are constructed without nondegeneracy inputs. -/
def_wanted relative_cy_cospan_class_maps (k : Type u) [Field k] (P : Cospan (k := k))
    (S : NegativeTraceSystem k) (n : ℤ) (D : ModuleData P S n) (T : CyclicData D)
    (a : CyclicData.Compatible (P := P) (S := S) (n := n)) : CospanClassMaps T a

/-- The native source-to-sum conversion negates every Y relative-class matrix block. -/
def_wanted relative_cy_negative_class_maps (k : Type u) [Field k] (A B : DGCat k)
    (S : NegativeTraceSystem k) (f : A ⟶ B) (DA : CYCategoryData S A) (DB : CYCategoryData S B)
    (F : RelativeCYContext S f DA DB) (n : ℤ) (a : RelativeNegativeClass S f n)
    (C : RelativeConeContext F n) (M : RelativeCYMapModel F n a C) : NegatedRelativeCYMaps M

/-- Multiplication by -1 preserves the three actual module quasi-isomorphisms. -/
theorem_wanted relative_cy_negation_nondegeneracy (k : Type u) [Field k] (A B : DGCat k)
    (S : NegativeTraceSystem k) (f : A ⟶ B) (DA : CYCategoryData S A) (DB : CYCategoryData S B)
    (F : RelativeCYContext S f DA DB) (n : ℤ) (a : RelativeNegativeClass S f n)
    (C : RelativeConeContext F n) (M : RelativeCYMapModel F n a C) (N : NegatedRelativeCYMaps M) :
  IsRelativeCalabiYau N.negated ↔ IsRelativeCalabiYau M

/-- Construction data for composing relative Calabi–Yau cospans (Brav–Dyckerhoff, Theorem 6.2). Let
$k$ be a field and `P` a diagram of DG categories over $k$ consisting of functors $e : A \to X$,
$f : B \to X$, $g : B \to Y$, $h : C \to Y$, $i : X \to Z$ and $j : Y \to Z$ with
$i \circ f = j \circ g$, such that the square formed by $f$, $g$, $i$ and $j$ is a Morita pushout
(for the DG frame system `R`). Let $n \in \mathbb{Z}$, let `S` be a negative cyclic trace system,
and fix bar and duality data `DA`, …, `DZ` (`CYCategoryData`) for the six categories, with $A$, $B$,
$C$, $X$ and $Y$ homologically smooth (no smoothness hypothesis on $Z$). This constructs a
`CospanTraceIntegration` with these data: module data, the cospan operations, the completed coherent
grid diagrams, the cyclic coefficient data and, for every compatible negative cyclic class, the
class-induced maps together with a joint comparison of the dual and shifted grid diagrams,
identified with the class maps pointwise up to homotopy. -/
def_wanted relative_cy_cospan_trace_integration (k : Type u) [Field k] (R : DGFrameSystem k)
    (P : Cospan (k := k)) (S : NegativeTraceSystem k) (n : ℤ)
    (DA : CYCategoryData S P.A) (DB : CYCategoryData S P.B) (DC : CYCategoryData S P.C)
    (DX : CYCategoryData S P.X) (DY : CYCategoryData S P.Y) (DZ : CYCategoryData S P.Z)
    (smoothA : IsHomologicallySmooth P.A DA.diagonal)
    (smoothB : IsHomologicallySmooth P.B DB.diagonal)
    (smoothC : IsHomologicallySmooth P.C DC.diagonal)
    (smoothX : IsHomologicallySmooth P.X DX.diagonal)
    (smoothY : IsHomologicallySmooth P.Y DY.diagonal)
    (pushout : IsMoritaPushout R P.f P.g P.i P.j P.square) :
  CospanTraceIntegration P S n DA DB DC DX DY DZ

/-- Source Theorem 6.2: the two relative CY projections give relative CY on the computed A/C composite.
The actual smoothness and all three target module quasi-isomorphisms are conclusions. -/
theorem_wanted relative_calabi_yau_cospan_composition (k : Type u) [Field k] (R : DGFrameSystem k)
    (P : Cospan (k := k)) (S : NegativeTraceSystem k) (n : ℤ)
    (DA : CYCategoryData S P.A) (DB : CYCategoryData S P.B) (DC : CYCategoryData S P.C)
    (DX : CYCategoryData S P.X) (DY : CYCategoryData S P.Y) (DZ : CYCategoryData S P.Z)
    (pushout : IsMoritaPushout R P.f P.g P.i P.j P.square)
    (I : CospanTraceIntegration P S n DA DB DC DX DY DZ)
    (a : CyclicData.Compatible (P := P) (S := S) (n := n))
    (leftCY : IsRelativeCalabiYau (I.realize a).classes.left)
    (rightCY : IsRelativeCalabiYau (I.realize a).classes.right) :
  IsRelativeCalabiYau (I.realize a).classes.outer

end WantedExt.AlgebraicGeometry.DGRelativeCYDiagramLedgerWanted
