/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeWittLoopCorrespondences
public import MathlibExt.CategoryTheory.SheafTorsorGroupoids
public import Mathlib.Algebra.Category.Grp.Ulift

/-!
# Actual left Witt-loop actions on the original Grassmannian quotient

The raw action is a natural map on the original loop presheaf and the
actual right-action coequalizer. Its value on every original loop class
is fixed by native group multiplication. The fpqc group sheaves retain
the original group-valued loop functors, and their descent condition is
a proof about those exact functors. The sheaf action has the actual
Grassmannian sheaf as target and retains unit, associativity and the
complete raw-to-sheaf action square.

The positive action is restriction through the original uniformizer
localization homomorphism. No separate positive-loop action is selected.

Source: Zhu, arXiv:1407.8519v3, Sections 1.1--1.2. The source-normalized
action and group-descent constructors are separate Wanted requests.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.WittQuotientActionModels

open _root_.CategoryTheory Opposite _root_.AlgebraicGeometry
open RelativeWittLoopTests RelativeWittLoopCorrespondences
open MathlibExt.CategoryTheory.SheafTorsorGroupoids

variable (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k]
  (B : Type) [CommRing B] [Algebra (WittVector p k) B] (pi : B)
  (G : Over (Spec (.of B))) [GrpObj G]

/-- The raw left action is fixed on every actual native loop class. -/
structure RawLeftAction where
  action : RelativeWittLoopCorrespondences.pairs p k (loopSets p k B pi G)
    (grassmannianPresheaf p k B pi G) ⟶ grassmannianPresheaf p k B pi G
  on_loops : ∀ (R : PerfectAlgebra p k) (g h : (loopSets p k B pi G).obj R),
    action.app R (g, (quotient p k B pi G).app R h) =
      (quotient p k B pi G).app R (g * h)
  unit : ∀ (R : PerfectAlgebra p k) (x : (grassmannianPresheaf p k B pi G).obj R),
    action.app R (1, x) = x
  associative : ∀ (R : PerfectAlgebra p k) (g h : (loopSets p k B pi G).obj R)
    (x : (grassmannianPresheaf p k B pi G).obj R),
    action.app R (g * h, x) = action.app R (g, action.app R (h, x))

/-- The original fpqc loop group presheaf, lifting only the value universe. -/
def loopGroups : ((PerfectAlgebra p k)ᵒᵖ)ᵒᵖ ⥤ GrpCat.{1} :=
  (opOpEquivalence (PerfectAlgebra p k)).functor ⋙ loops p k B pi G ⋙
    GrpCat.uliftFunctor.{1, 0}

/-- The original positive-loop group presheaf on the very same residue tests. -/
def positiveGroups : ((PerfectAlgebra p k)ᵒᵖ)ᵒᵖ ⥤ GrpCat.{1} :=
  (opOpEquivalence (PerfectAlgebra p k)).functor ⋙ positiveLoops p k B G ⋙
    GrpCat.uliftFunctor.{1, 0}

/-- Descent refers to the original loop-group point functor. -/
abbrev LoopDescent := Presheaf.IsSheaf (fpqcTopology p k) (loopGroups p k B pi G)

/-- Descent refers to the original positive-loop point functor. -/
abbrev PositiveDescent := Presheaf.IsSheaf (fpqcTopology p k) (positiveGroups p k B G)

/-- The actual loop-group sheaf contains the original point groups and restrictions. -/
def loopGroupSheaf (H : LoopDescent p k B pi G) :
    Sheaf (fpqcTopology p k) GrpCat.{1} := ⟨loopGroups p k B pi G, H⟩

/-- The actual positive-loop sheaf retains those same native coefficient maps. -/
def positiveGroupSheaf (H : PositiveDescent p k B G) :
    Sheaf (fpqcTopology p k) GrpCat.{1} := ⟨positiveGroups p k B G, H⟩

/-- The original group inclusion is the actual uniformizer-localization map. -/
def groupInclusion : positiveGroups p k B G ⟶ loopGroups p k B pi G :=
  Functor.whiskerLeft (opOpEquivalence (PerfectAlgebra p k)).functor
    (Functor.whiskerRight (positiveToLoop p k B pi G) GrpCat.uliftFunctor.{1, 0})

/-- The actual raw Grassmannian insertion into its native fpqc sheafification. -/
def quotientUnit :
    (opOpEquivalence (PerfectAlgebra p k)).functor ⋙ grassmannianPresheaf p k B pi G ⟶
      (grassmannian p k B pi G).obj :=
  toSheafify (fpqcTopology p k) _

/-- The sheaf action retains all group sections and the exact source action square. -/
structure SheafLeftAction (H : LoopDescent p k B pi G)
    (A : RawLeftAction p k B pi G) where
  action : MathlibExt.CategoryTheory.SheafTorsorGroupoids.pairs
    (groupSets (fpqcTopology p k) (loopGroupSheaf p k B pi G H)).obj
      (grassmannian p k B pi G).obj ⟶ (grassmannian p k B pi G).obj
  unit : ∀ (T : ((PerfectAlgebra p k)ᵒᵖ)ᵒᵖ)
    (x : (grassmannian p k B pi G).obj.obj T), action.app T (1, x) = x
  associative : ∀ (T : ((PerfectAlgebra p k)ᵒᵖ)ᵒᵖ)
    (g h : (groupSets (fpqcTopology p k) (loopGroupSheaf p k B pi G H)).obj.obj T)
    (x : (grassmannian p k B pi G).obj.obj T),
    action.app T (g * h, x) = action.app T (g, action.app T (h, x))
  normalized : ∀ (R : PerfectAlgebra p k) (g : (loopSets p k B pi G).obj R)
    (x : (grassmannianPresheaf p k B pi G).obj R),
    action.app (op (op R)) (g, (quotientUnit p k B pi G).app (op (op R)) x) =
      (quotientUnit p k B pi G).app (op (op R)) (A.action.app R (g, x))

/-- All actual loop actions and their descent proofs are native construction outputs. -/
structure QuotientActions where
  raw : RawLeftAction p k B pi G
  loopDescent : LoopDescent p k B pi G
  positiveDescent : PositiveDescent p k B G
  sheaf : SheafLeftAction p k B pi G loopDescent raw

/-- Positive action is the native original inclusion followed by this same loop action. -/
def positiveAction (A : QuotientActions p k B pi G) :
    MathlibExt.CategoryTheory.SheafTorsorGroupoids.pairs
      (groupSets (fpqcTopology p k) (positiveGroupSheaf p k B G A.positiveDescent)).obj
        (grassmannian p k B pi G).obj ⟶ (grassmannian p k B pi G).obj where
  app T := ↾fun x ↦ A.sheaf.action.app T ((groupInclusion p k B pi G).app T x.1, x.2)
  naturality {T U} f := by
    apply ConcreteCategory.hom_ext
    intro x
    have h := ConcreteCategory.congr_hom ((groupInclusion p k B pi G).naturality f) x.1
    change (groupInclusion p k B pi G).app U ((positiveGroups p k B G).map f x.1) =
      (loopGroups p k B pi G).map f ((groupInclusion p k B pi G).app T x.1) at h
    have a : A.sheaf.action.app U
        ((loopGroups p k B pi G).map f ((groupInclusion p k B pi G).app T x.1),
          (grassmannian p k B pi G).obj.map f x.2) =
      (grassmannian p k B pi G).obj.map f
        (A.sheaf.action.app T ((groupInclusion p k B pi G).app T x.1, x.2)) :=
      congrArg (fun u ↦ u ((groupInclusion p k B pi G).app T x.1, x.2))
        (A.sheaf.action.naturality f)
    change A.sheaf.action.app U
      ((groupInclusion p k B pi G).app U ((positiveGroups p k B G).map f x.1),
        (grassmannian p k B pi G).obj.map f x.2) =
      (grassmannian p k B pi G).obj.map f
        (A.sheaf.action.app T ((groupInclusion p k B pi G).app T x.1, x.2))
    exact (congrArg (fun y ↦ A.sheaf.action.app U
      (y, (grassmannian p k B pi G).obj.map f x.2)) h).trans a

/-- The positive action has the actual native group unit. -/
theorem positiveAction_unit (A : QuotientActions p k B pi G)
    (T : ((PerfectAlgebra p k)ᵒᵖ)ᵒᵖ) (x : (grassmannian p k B pi G).obj.obj T) :
    (positiveAction p k B pi G A).app T (1, x) = x := by
  change A.sheaf.action.app T ((groupInclusion p k B pi G).app T 1, x) = x
  rw [map_one]
  exact A.sheaf.unit T x

/-- Positive-loop associativity is inherited through the original group homomorphism. -/
theorem positiveAction_associative (A : QuotientActions p k B pi G)
    (T : ((PerfectAlgebra p k)ᵒᵖ)ᵒᵖ)
    (g h : (positiveGroups p k B G).obj T)
    (x : (grassmannian p k B pi G).obj.obj T) :
    (positiveAction p k B pi G A).app T (g * h, x) =
      (positiveAction p k B pi G A).app T
        (g, (positiveAction p k B pi G A).app T (h, x)) := by
  change A.sheaf.action.app T ((groupInclusion p k B pi G).app T (g * h), x) =
    A.sheaf.action.app T ((groupInclusion p k B pi G).app T g,
      A.sheaf.action.app T ((groupInclusion p k B pi G).app T h, x))
  rw [map_mul]
  exact A.sheaf.associative T _ _ x

end MathlibExt.AlgebraicGeometry.WittQuotientActionModels
