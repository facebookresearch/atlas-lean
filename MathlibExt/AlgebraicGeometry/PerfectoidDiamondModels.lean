/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import MathlibExt.AlgebraicGeometry.PerfectoidLocalModels

/-!
# Actual perfectoid atlas and diamond quotient models

Global objects are genuine v-sheaves on the actual affine perfectoid
basis. Their charts are monomorphisms from affine representables. Every
chart pullback to an affine test is covered by the specified rational
algebras, with both legs induced by actual bounded ring maps.

Pro-etale maps are checked on these affine pullbacks and use the actual
local pro-etale presentations. A diamond presentation is a representable
pro-etale equivalence relation, and its quotient is the actual sheaf
coequalizer. No freely named space, groupoid or sheaf carrier is given.

References: Scholze, arXiv:1709.07343v4, Definitions 8.1, 11.1--11.2
and Proposition 11.3. Affine/v representability and global atlas
realization are source-model comparison inputs, separate from generic
adic gluing and from the quotient theorem.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PerfectoidDiamondModels

open CategoryTheory CategoryTheory.Limits
open MathlibExt.RingTheory.CompleteHuberPairModels
open AffinePerfectoidVSite PerfectoidLocalModels

variable (p : ℕ) [Fact p.Prime]

/-- Lift the actual affine Hom sets only to the site's sheaf universe. -/
def liftTypes : Type ⥤ Type 1 := uliftFunctor.{1, 0}

/-- The actual sheafified affine representable. -/
def affineSheaf (P : Affine p) : VSheaf p :=
  (presheafToSheaf (topology p) (Type 1)).obj
    (yoneda.obj P ⋙ liftTypes)

/-- A genuine bounded affine morphism gives this prescribed sheaf map. -/
def affineMap {P Q : Affine p} (f : P ⟶ Q) :
    affineSheaf p P ⟶ affineSheaf p Q :=
  (presheafToSheaf (topology p) (Type 1)).map
    (Functor.whiskerRight (yoneda.map f) liftTypes)

/-- Joint epimorphy of an actual family, without a chosen quotient carrier. -/
def JointlyEpi {ι : Type 1} {F : VSheaf p} (U : ι → VSheaf p)
    (f : ∀ i, U i ⟶ F) : Prop :=
  ∀ (G : VSheaf p) (a b : F ⟶ G),
    (∀ i, f i ≫ a = f i ≫ b) → a = b

/-- A rational chart lift into an actual affine pullback. -/
def chartLift {P Q : Affine p} {F : VSheaf p}
    (m : affineSheaf p P ⟶ F) (a : affineSheaf p Q ⟶ F)
    (D : RationalModel p Q) (g : D.affine ⟶ P)
    (h : affineMap p g ≫ m = affineMap p D.map ≫ a) :
    affineSheaf p D.affine ⟶ pullback m a :=
  pullback.lift (affineMap p g) (affineMap p D.map) h

/-- The exact open-affine chart condition on every affine base change. -/
def IsOpenChart {P : Affine p} {F : VSheaf p}
    (m : affineSheaf p P ⟶ F) : Prop :=
  Mono m ∧ ∀ (Q : Affine p) (a : affineSheaf p Q ⟶ F),
    ∃ ι : Type 1, ∃ D : ι → RationalModel p Q,
      ∃ g : ∀ i, (D i).affine ⟶ P,
      ∃ h : ∀ i, affineMap p (g i) ≫ m = affineMap p (D i).map ≫ a,
      JointlyEpi p (fun i ↦ affineSheaf p (D i).affine)
        (fun i ↦ chartLift p m a (D i) (g i) (h i))

/-- An actual affine-open atlas of a v-sheaf. -/
structure OpenAtlas (F : VSheaf p) where
  index : Type 1
  affine : index → Affine p
  chart : ∀ i, affineSheaf p (affine i) ⟶ F
  open_chart : ∀ i, IsOpenChart p (chart i)
  covers : JointlyEpi p (fun i ↦ affineSheaf p (affine i)) chart

/-- A global perfectoid model, specified by its actual v-sheaf/open atlas. -/
structure PerfectoidSpace where
  sheaf : VSheaf p
  atlas : OpenAtlas p sheaf

instance : Category (PerfectoidSpace p) where
  Hom X Y := X.sheaf ⟶ Y.sheaf
  id X := 𝟙 X.sheaf
  comp f g := f ≫ g

/-- A pro-etale morphism has actual locally presented affine pullbacks. -/
def IsProEtaleMap {X Y : PerfectoidSpace p}
    (f : X.sheaf ⟶ Y.sheaf) : Prop :=
  ∀ (Q : Affine p) (a : affineSheaf p Q ⟶ Y.sheaf),
    ∃ A : OpenAtlas p (pullback f a),
      ∃ g : ∀ i, A.affine i ⟶ Q,
        (∀ i, A.chart i ≫ pullback.snd f a = affineMap p (g i)) ∧
        (∀ i, PerfectoidLocalModels.IsProEtale p (g i))

/-- A representable pro-etale equivalence relation on the actual models. -/
structure Relation where
  X : PerfectoidSpace p
  R : PerfectoidSpace p
  source : R.sheaf ⟶ X.sheaf
  target : R.sheaf ⟶ X.sheaf
  mono : Mono (prod.lift source target)
  source_proetale : IsProEtaleMap p (X := R) (Y := X) source
  target_proetale : IsProEtaleMap p (X := R) (Y := X) target
  reflexivity : ∃ e : X.sheaf ⟶ R.sheaf,
    e ≫ source = 𝟙 X.sheaf ∧ e ≫ target = 𝟙 X.sheaf
  symmetry : ∃ i : R.sheaf ⟶ R.sheaf,
    i ≫ source = target ∧ i ≫ target = source
  transitivity : ∃ m : pullback target source ⟶ R.sheaf,
    m ≫ source = pullback.fst target source ≫ source ∧
    m ≫ target = pullback.snd target source ≫ target

/-- The quotient is the actual coequalizer in v-sheaves. -/
def Relation.quotient (R : Relation p) : VSheaf p :=
  coequalizer R.source R.target

/-- A diamond model with its prescribed representable quotient. -/
structure Diamond where
  sheaf : VSheaf p
  relation : Relation p
  quotient_iso : Relation.quotient p relation ≅ sheaf

end MathlibExt.AlgebraicGeometry.PerfectoidDiamondModels
