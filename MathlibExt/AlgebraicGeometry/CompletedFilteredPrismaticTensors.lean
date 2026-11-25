/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SyntomicNearbyComparisons
public import Mathlib.Algebra.Homology.HomotopyCofiber

/-!
# Completed filtered tensors of the actual finite prismatic quotient lines

The completed filtered tensor is the resolved Milnor limit of the actual
relative module-presheaf tensor on each finite Nygaard quotient ring.
Its inverse evaluation is induced by the original finite line/dual
evaluation maps and the actual quotient-coefficient transitions. The
line, dual and unit realizations use the same finite tower and native
K-injective resolution. All maps on limits are native product-square,
mapping-cone and shift maps.

Completion comparison is the actual sheafification counit inverse and
resolution unit on every finite quotient. Identifying these realizations
with the source's complete filtered derived theory is a separate Wanted
endpoint. No unfiltered invertibility is asserted.

Source: BMS19 arXiv:1802.03261v2, Theorem1.12(3), footnote3 and
Section7.4; Bhatt–Scholze arXiv:1905.08229v4, Sections12–15.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 60000
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CompletedFilteredPrismaticTensors

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open AbsolutePrismaticBasis PrismaticFilteredTwists
open SyntomicNearbyComparisons
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard

structure Tower (M : Type 2) [Category.{1} M] [Abelian M] where
  level : ℕ → CochainComplex M ℤ
  step : ∀ n, level (n + 1) ⟶ level n

namespace Tower

variable {M : Type 2} [Category.{1} M] [Abelian M]

structure Hom (X Y : Tower M) where
  map : ∀ n, X.level n ⟶ Y.level n
  commutes : ∀ n, X.step n ≫ map n = map (n + 1) ≫ Y.step n

variable [HasLimitsOfShape (Discrete ℕ) M] (X : Tower M)

def difference : ∏ᶜ X.level ⟶ ∏ᶜ X.level :=
  Pi.lift.{0,1,2} (fun n ↦ Pi.π.{0,1,2} X.level n - Pi.π.{0,1,2} X.level (n + 1) ≫ X.step n)

def milnor : CochainComplex M ℤ := CochainComplex.mappingCocone X.difference

def projection (n : ℕ) : X.milnor ⟶ X.level n :=
  CochainComplex.mappingCocone.fst X.difference ≫ Pi.π.{0,1,2} X.level n

variable {X} {Y : Tower M} (f : Hom X Y)

def productMap : ∏ᶜ X.level ⟶ ∏ᶜ Y.level :=
  Pi.lift.{0,1,2} (fun n ↦ Pi.π.{0,1,2} X.level n ≫ f.map n)

theorem square : productMap f ≫ Y.difference = X.difference ≫ productMap f := by
  apply Pi.hom_ext
  intro n
  simp only [difference, productMap, Category.assoc, Pi.lift_comp_π, Pi.lift_comp_π_assoc, Preadditive.comp_sub,
    Preadditive.sub_comp]
  rw [f.commutes n]

/-- Functorial Milnor map is the native cone map of the actual product square, shifted by −1. -/
def map : X.milnor ⟶ Y.milnor :=
  (shiftFunctor (CochainComplex M ℤ) (-1 : ℤ)).map
    (HomologicalComplex.homotopyCofiber.mapArrowHom X.difference Y.difference
      (fun j : ℤ ↦ ⟨j - 1, by simp⟩) (Arrow.homMk (productMap f) (productMap f) (square f)))

variable (R : FunctorialKInjective M)

def resolved (X : Tower M) : Tower M where
  level n := R.functor.obj (X.level n)
  step n := R.functor.map (X.step n)

def resolveHom (f : Hom X Y) : Hom (resolved R X) (resolved R Y) where
  map n := R.functor.map (f.map n)
  commutes n := by
    change R.functor.map (X.step n) ≫ R.functor.map (f.map n) =
      R.functor.map (f.map (n + 1)) ≫ R.functor.map (Y.step n)
    rw [← R.functor.map_comp, f.commutes n, R.functor.map_comp]

end Tower

/-- Scalar restriction is normalized before specializing the actual
large prismatic coefficient functor. -/
def finiteDualStepValue {C : Type 1} [Category.{0} C]
    {coeff : ℕ → Cᵒᵖ ⥤ CommRingCat.{0}} {q : ∀ n : ℕ, coeff (n + 1) ⟶ coeff n}
    {J : GrothendieckTopology C} (L : FiniteLineTower coeff q J)
    (n : ℕ) (B : Cᵒᵖ) (f : (L.dual (n + 1)).obj B) : (L.dual n).obj B :=
  ((L.dualTransition n).app B).hom f

def finiteLineStepValue {C : Type 1} [Category.{0} C]
    {coeff : ℕ → Cᵒᵖ ⥤ CommRingCat.{0}} {q : ∀ n : ℕ, coeff (n + 1) ⟶ coeff n}
    {J : GrothendieckTopology C} (L : FiniteLineTower coeff q J)
    (n : ℕ) (B : Cᵒᵖ) (x : (L.line (n + 1)).obj B) : (L.line n).obj B :=
  ((L.lineTransition n).app B).hom x

variable (p : ℕ) [Fact p.Prime] (A : QuasiSyntomicPrismSites.Ring p)
  (D : ∀ B : Basis p A, InitialLift p (ring p B))
  (Z : ZeroReduction p A D) (T : TwistTower p A D Z)

abbrev Sheaves := PrismaticNygaardCohomology.Sheaves p A

instance countableSheafLimits : HasLimitsOfShape (Discrete ℕ) (Sheaves p A) := by
  let : HasLimitsOfShape (Discrete ℕ) (ModuleCat.{1} ℤ) := ModuleCat.hasLimitsOfShape
  exact @Sheaf.instHasLimitsOfShape.{2,1,0,1,0,0}
    (Basis p A)ᵒᵖ inferInstance (topology p A) (ModuleCat.{1} ℤ) inferInstance
      (Discrete ℕ) inferInstance inferInstance

def finiteTensorPresheaf (n : ℕ) : ((Basis p A)ᵒᵖ)ᵒᵖ ⥤ ModuleCat.{1} ℤ :=
  (integers p A D n).obj (PresheafOfModulesOfCommRing.Monoidal.tensorObj (T.data.dual n) (T.data.line n))

def finiteEvaluationPresheaf (n : ℕ) : finiteTensorPresheaf p A D Z T n ≅ (T.finiteSheaf n 0).obj :=
  (integers p A D n).mapIso (T.data.evaluation n)

/-- The inverse pair is the original signed −1 and +1 word, via the
native unitors of the relative quotient-module tensor. -/
def signedPairIso (n : ℕ) :
    (integers p A D n).obj ((T.finite n (-1)) ⊗ (T.finite n 1)) ≅
      finiteTensorPresheaf p A D Z T n :=
  (integers p A D n).mapIso
    (whiskerRightIso (ρ_ (T.data.dual n)) (T.finite n 1) ≪≫
      whiskerLeftIso (T.data.dual n) (ρ_ (T.data.line n)))

def tensorPresheafStep (n : ℕ) : finiteTensorPresheaf p A D Z T (n + 1) ⟶ finiteTensorPresheaf p A D Z T n :=
  (finiteEvaluationPresheaf p A D Z T (n + 1)).hom ≫ (T.finiteSheafTransition n 0).hom ≫
    (finiteEvaluationPresheaf p A D Z T n).inv

/-- Full pure-tensor normalization over every actual finite quotient.
This certifies the fixed evaluation-conjugate map against the original
dual and line transitions, using their actual coefficient quotient map. -/
structure TensorTransitionNormalization : Prop where
  pure_tensor : ∀ (n : ℕ) (B : ((Basis p A)ᵒᵖ)ᵒᵖ)
    (f : (T.data.dual (n + 1)).obj B) (x : (T.data.line (n + 1)).obj B),
    ((tensorPresheafStep p A D Z T n).app B).hom
      (ULift.up (f ⊗ₜ[(quotientPresheaf p A D (n + 1)).obj B] x)) =
    ULift.up (finiteDualStepValue T.data n B f ⊗ₜ[(quotientPresheaf p A D n).obj B]
      finiteLineStepValue T.data n B x)

def finiteTensor (n : ℕ) : Sheaves p A :=
  (presheafToSheaf (topology p A) (ModuleCat.{1} ℤ)).obj (finiteTensorPresheaf p A D Z T n)

def finiteWord (i : ℤ) (n : ℕ) : Sheaves p A :=
  (presheafToSheaf (topology p A) (ModuleCat.{1} ℤ)).obj (T.finiteSheaf n i).obj

def finiteEvaluation (n : ℕ) : finiteTensor p A D Z T n ≅ finiteWord p A D Z T 0 n :=
  (presheafToSheaf (topology p A) (ModuleCat.{1} ℤ)).mapIso (finiteEvaluationPresheaf p A D Z T n)

def tensorTower : Tower (Sheaves p A) where
  level n := (HomologicalComplex.single (Sheaves p A) (.up ℤ) 0).obj (finiteTensor p A D Z T n)
  step n := (HomologicalComplex.single (Sheaves p A) (.up ℤ) 0).map
    ((presheafToSheaf (topology p A) (ModuleCat.{1} ℤ)).map (tensorPresheafStep p A D Z T n))

def wordTower (i : ℤ) : Tower (Sheaves p A) where
  level n := (HomologicalComplex.single (Sheaves p A) (.up ℤ) 0).obj (finiteWord p A D Z T i n)
  step n := (HomologicalComplex.single (Sheaves p A) (.up ℤ) 0).map
    ((presheafToSheaf (topology p A) (ModuleCat.{1} ℤ)).map (T.finiteSheafTransition n i).hom)

def evaluationTower : Tower.Hom (tensorTower p A D Z T) (wordTower p A D Z T 0) where
  map n := (HomologicalComplex.single (Sheaves p A) (.up ℤ) 0).map (finiteEvaluation p A D Z T n).hom
  commutes n := by
    let S := presheafToSheaf (topology p A) (ModuleCat.{1} ℤ)
    let C := HomologicalComplex.single (Sheaves p A) (.up ℤ) 0
    change C.map (S.map (tensorPresheafStep p A D Z T n)) ≫
      C.map (S.map (finiteEvaluationPresheaf p A D Z T n).hom) =
      C.map (S.map (finiteEvaluationPresheaf p A D Z T (n + 1)).hom) ≫
      C.map (S.map (T.finiteSheafTransition n 0).hom)
    rw [← C.map_comp, ← C.map_comp, ← S.map_comp, ← S.map_comp]
    exact congrArg C.map (congrArg S.map (by
      dsimp only [tensorPresheafStep]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]))

variable (R : FunctorialKInjective (Sheaves p A))

/-- Completed filtered tensor of the inverse pair, using the original relative quotient tensors. -/
def completedTensor : DerivedCategory (Sheaves p A) :=
  DerivedCategory.Q.obj (Tower.resolved R (tensorTower p A D Z T)).milnor

/-- The same resolved derived-limit realization for every signed source word. -/
def completedWord (i : ℤ) : DerivedCategory (Sheaves p A) :=
  DerivedCategory.Q.obj (Tower.resolved R (wordTower p A D Z T i)).milnor

def completedEvaluation : completedTensor p A D Z T R ⟶ completedWord p A D Z T R 0 :=
  DerivedCategory.Q.map (Tower.map (Tower.resolveHom R (evaluationTower p A D Z T)))

def completedTensorProjection (n : ℕ) : completedTensor p A D Z T R ⟶
    DerivedCategory.Q.obj ((Tower.resolved R (tensorTower p A D Z T)).level n) :=
  DerivedCategory.Q.map ((Tower.resolved R (tensorTower p A D Z T)).projection n)

def completedWordProjection (i : ℤ) (n : ℕ) : completedWord p A D Z T R i ⟶
    DerivedCategory.Q.obj ((Tower.resolved R (wordTower p A D Z T i)).level n) :=
  DerivedCategory.Q.map ((Tower.resolved R (wordTower p A D Z T i)).projection n)

def rawTower (i : ℤ) : Tower (Sheaves p A) where
  level := T.levelComplex i
  step := T.levelTransition i

def finiteCompletionMap (i : ℤ) (n : ℕ) : (rawTower p A D Z T i).level n ⟶
    (Tower.resolved R (wordTower p A D Z T i)).level n :=
  (HomologicalComplex.single (Sheaves p A) (.up ℤ) 0).map
    ((asIso ((sheafificationAdjunction (topology p A) (ModuleCat.{1} ℤ)).counit)).inv.app (T.finiteSheaf n i)) ≫
      R.unit.app ((wordTower p A D Z T i).level n)

/-- The finite completion maps are fixed native maps; only their source
commuting-square proof is an implementation input. -/
structure CompletionMaps where
  commutes : ∀ (i : ℤ) (n : ℕ),
    (rawTower p A D Z T i).step n ≫ finiteCompletionMap p A D Z T R i n =
      finiteCompletionMap p A D Z T R i (n + 1) ≫ (Tower.resolved R (wordTower p A D Z T i)).step n

namespace CompletionMaps

variable {p A D Z T R} (C : CompletionMaps p A D Z T R)

def tower (i : ℤ) : Tower.Hom (rawTower p A D Z T i) (Tower.resolved R (wordTower p A D Z T i)) :=
  ⟨finiteCompletionMap p A D Z T R i, C.commutes i⟩

def sourceProductMap (_C : CompletionMaps p A D Z T R) (i : ℤ) : T.productComplex i ⟶
    ∏ᶜ (Tower.resolved R (wordTower p A D Z T i)).level :=
  Pi.lift.{0,1,2} (fun n ↦ Pi.π.{0,1,2} (T.levelComplex i) n ≫ finiteCompletionMap p A D Z T R i n)

theorem sourceSquare (i : ℤ) :
    C.sourceProductMap i ≫ (Tower.resolved R (wordTower p A D Z T i)).difference =
      T.difference i ≫ C.sourceProductMap i := by
  apply Pi.hom_ext.{0,1,2} (C := CochainComplex (Sheaves p A) ℤ)
    (f := (Tower.resolved R (wordTower p A D Z T i)).level)
  intro n
  simp only [sourceProductMap, Tower.difference, TwistTower.difference, Category.assoc,
    Pi.lift_comp_π, Pi.lift_comp_π_assoc, Preadditive.comp_sub, Preadditive.sub_comp]
  have h := C.commutes i n
  change T.levelTransition i n ≫ finiteCompletionMap p A D Z T R i n =
    finiteCompletionMap p A D Z T R i (n + 1) ≫
      (Tower.resolved R (wordTower p A D Z T i)).step n at h
  rw [h]

/-- Native cone/shift map uses the original source product and difference
directly, with every finite completion map in the actual product square. -/
def comparison (i : ℤ) : DerivedCategory.Q.obj (T.complex i) ⟶ completedWord p A D Z T R i :=
  DerivedCategory.Q.map ((shiftFunctor (CochainComplex (Sheaves p A) ℤ) (-1 : ℤ)).map
    (HomologicalComplex.homotopyCofiber.mapArrowHom (T.difference i)
      (Tower.resolved R (wordTower p A D Z T i)).difference
      (fun j : ℤ ↦ ⟨j - 1, by simp⟩)
      (Arrow.homMk (C.sourceProductMap i) (C.sourceProductMap i) (C.sourceSquare i))))

end CompletionMaps

/-- Inverse property of the completed twist tower: for a prime $p$, a quasisyntomic ring $A$ with
initial prisms $D$ on its basis and zero-step reduction $Z$, a twist tower $T$ (lines $L_n$ and
duals $L_n^\vee$ over the finite quotient coefficient rings), a functorial K-injective resolution
$R$ and completion maps $C$, where completions are the Milnor complexes (derived limits) of the
$R$-resolved towers. It asserts: the completed evaluation map, induced by the level-$n$ evaluation
maps from the sheafified tensor product $L_n^\vee \otimes L_n$ to the weight-$0$ sheaf, is an
isomorphism in the derived category; it commutes with the projections to every level $n$, through
the resolved level-$n$ evaluation map; and for every weight $i$ and level $n$, the comparison
`C.comparison i` from the Milnor complex of the unresolved weight-$i$ tower to its completion,
followed by the projection to level $n$, is the projection to level $n$ followed by the level-$n$
completion map `finiteCompletionMap`. -/
structure CompletedFilteredInverse (C : CompletionMaps p A D Z T R) : Prop where
  evaluation_isIso : IsIso (completedEvaluation p A D Z T R)
  evaluation_projections : ∀ n : ℕ,
    completedEvaluation p A D Z T R ≫ completedWordProjection p A D Z T R 0 n =
      completedTensorProjection p A D Z T R n ≫
        DerivedCategory.Q.map (R.functor.map ((evaluationTower p A D Z T).map n))
  completion_projections : ∀ (i : ℤ) (n : ℕ),
    C.comparison i ≫ completedWordProjection p A D Z T R i n =
      DerivedCategory.Q.map (T.projection i n) ≫
        DerivedCategory.Q.map (finiteCompletionMap p A D Z T R i n)

end MathlibExt.AlgebraicGeometry.CompletedFilteredPrismaticTensors
