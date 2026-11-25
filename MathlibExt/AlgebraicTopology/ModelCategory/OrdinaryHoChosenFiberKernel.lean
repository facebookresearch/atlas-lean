/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyCategory
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenOrdinaryHoReplacement
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Chosen-fiber image exactness in the ordinary homotopy category

In an already constructed model category, the caller's actual zero object
and actual limiting cone are retained. A fibration over a fibrant base
makes the total and fiber objects fibrant. The fundamental lemma represents
each Ho arrow from a cofibrant coefficient. The model's actual covering
homotopy lifts its null composite and gives a literal zero representative
in that same chosen fiber.

Actual replacement inverse functions transport this image/null-fiber law
to every coefficient. The image of first-leg precomposition equals the
null subset, giving a surjective map into that subset. The lifts supplied
here need not be unique. The proof uses the model's covering homotopy and
replacement maps.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace HomotopicalAlgebra.OrdinaryHoChosenFiberKernel

variable {C : Type u} [Category.{v} C]

variable (Z : C) (hZ : IsZero Z)

/-- The complete original zero function uses the actual caller's terminal and initial legs. -/
def nullMap (K B : C) : K ⟶ B := hZ.isTerminal.from K ≫ hZ.isInitial.to B

/-- Every actual coefficient map preserves the entire original zero function. -/
theorem nullMap_precomp {K K' B : C} (a : K' ⟶ K) :
    a ≫ nullMap Z hZ K B = nullMap Z hZ K' B := by
  unfold nullMap
  rw [← Category.assoc]
  exact congrArg (fun q => q ≫ hZ.isInitial.to B) (hZ.isTerminal.hom_ext _ _)

/-- Every actual target map preserves the entire original zero function. -/
theorem nullMap_postcomp {K E B : C} (p : E ⟶ B) :
    nullMap Z hZ K E ≫ p = nullMap Z hZ K B := by
  unfold nullMap
  rw [Category.assoc]
  exact congrArg (fun q => hZ.isTerminal.from K ≫ q) (hZ.isInitial.hom_ext _ _)

/-- Every actual map into the chosen fiber has the entire original zero projection. -/
theorem chosenFiberMap_over_zero {K E B : C} (p : E ⟶ B)
    (s : PullbackCone p (hZ.isInitial.to B)) (f : K ⟶ s.pt) :
    (f ≫ s.fst) ≫ p = nullMap Z hZ K B := by
  calc
    (f ≫ s.fst) ≫ p = (f ≫ s.snd) ≫ hZ.isInitial.to B := by
      rw [Category.assoc, s.condition, ← Category.assoc]
    _ = nullMap Z hZ K B :=
      congrArg (fun q => q ≫ hZ.isInitial.to B) (hZ.isTerminal.hom_ext _ _)

variable [ModelCategory C]

/-- The actual caller's zero object is fibrant by its original terminal universal property. -/
theorem zero_isFibrant (Z : C) (hZ : IsZero Z) : IsFibrant Z :=
  (isFibrant_iff_of_isTerminal (𝟙 Z) hZ.isTerminal).2 inferInstance

/-- The actual given fiber is fibrant by the original pullback and actual base-change axiom. -/
theorem chosenFiber_isFibrant {E B : C} (p : E ⟶ B) [Fibration p]
    (s : PullbackCone p (hZ.isInitial.to B)) (hs : IsLimit s) : IsFibrant s.pt := by
  let : IsFibrant Z := zero_isFibrant Z hZ
  have hp : IsPullback s.fst s.snd p (hZ.isInitial.to B) := IsPullback.of_isLimit hs
  let : Fibration s.snd := (fibration_iff s.snd).2
    ((fibrations C).of_isPullback hp ((fibration_iff p).1 inferInstance))
  exact isFibrant_of_fibration s.snd

/-- The whole geometric lift data retain the actual representative, both legs and homotopies. -/
structure KernelLiftData {E B : C} (K : C) (p : E ⟶ B)
    (s : PullbackCone p (hZ.isInitial.to B)) (f : K ⟶ E) where
  /-- The actual second endpoint of the lifted homotopy. -/
  representative : K ⟶ E
  /-- The actual limiting-cone lift into the caller's same chosen fiber. -/
  fiberMap : K ⟶ s.pt
  /-- Its entire original first leg is the actual second endpoint. -/
  fiber_fst : fiberMap ≫ s.fst = representative
  /-- Its entire original point leg is the actual terminal-zero map. -/
  fiber_snd : fiberMap ≫ s.snd = hZ.isTerminal.from K
  /-- The entire endpoint composite is the original literal zero function. -/
  representative_over : representative ≫ p = nullMap Z hZ K B
  /-- The full original left homotopy relates the original and lifted representatives. -/
  leftHomotopy : LeftHomotopyRel f representative
  /-- The full original right homotopy relates those same representatives. -/
  rightHomotopy : RightHomotopyRel f representative

/-- Actual model covering homotopy and the supplied limit construct the entire geometric lift. -/
theorem nonemptyKernelLiftData {E B : C} (K : C) [IsCofibrant K]
    (p : E ⟶ B) [Fibration p] [IsFibrant B]
    (s : PullbackCone p (hZ.isInitial.to B)) (hs : IsLimit s) (f : K ⟶ E)
    (hf : ((weakEquivalences C).Q).map (f ≫ p) = ((weakEquivalences C).Q).map (nullMap Z hZ K B)) :
    Nonempty (KernelLiftData Z hZ K p s f) := by
  let : IsFibrant E := isFibrant_of_fibration p
  have hRight : RightHomotopyRel (f ≫ p) (nullMap Z hZ K B) :=
    (RightHomotopyRel.iff_map_eq ((weakEquivalences C).Q) (X := K) (Y := B)).2 hf
  obtain ⟨P, hP, ⟨h⟩⟩ := hRight.leftHomotopyRel.exists_good_cylinder
  let : P.IsGood := hP
  obtain ⟨g, hLift, hOver⟩ := h.covering_homotopy p f rfl
  have hg : g ≫ p = nullMap Z hZ K B := by
    rw [← hLift.h₁, Category.assoc, hOver]
    exact h.h₁
  let c : PullbackCone p (hZ.isInitial.to B) :=
    PullbackCone.mk g (hZ.isTerminal.from K) hg
  exact ⟨{
    representative := g
    fiberMap := hs.lift c
    fiber_fst := hs.fac c WalkingCospan.left
    fiber_snd := hs.fac c WalkingCospan.right
    representative_over := hg
    leftHomotopy := hLift.leftHomotopyRel
    rightHomotopy := hLift.leftHomotopyRel.rightHomotopyRel }⟩

/-- The actual complete geometric lift chooses exactly the constructed data with the same inputs. -/
def kernelLiftData {E B : C} (K : C) [IsCofibrant K]
    (p : E ⟶ B) [Fibration p] [IsFibrant B]
    (s : PullbackCone p (hZ.isInitial.to B)) (hs : IsLimit s) (f : K ⟶ E)
    (hf : ((weakEquivalences C).Q).map (f ≫ p) = ((weakEquivalences C).Q).map (nullMap Z hZ K B)) :
    KernelLiftData Z hZ K p s f :=
  Classical.choice (nonemptyKernelLiftData Z hZ K p s hs f hf)

/-- The whole chosen first-leg Ho function reconstructs the actual original representative. -/
theorem kernelLiftData_ho_fac {E B : C} (K : C) [IsCofibrant K]
    (p : E ⟶ B) [Fibration p] [IsFibrant B]
    (s : PullbackCone p (hZ.isInitial.to B)) (hs : IsLimit s) (f : K ⟶ E)
    (hf : ((weakEquivalences C).Q).map (f ≫ p) = ((weakEquivalences C).Q).map (nullMap Z hZ K B)) :
    ((weakEquivalences C).Q).map (kernelLiftData Z hZ K p s hs f hf).fiberMap ≫
      ((weakEquivalences C).Q).map s.fst = ((weakEquivalences C).Q).map f := by
  rw [← ((weakEquivalences C).Q).map_comp, (kernelLiftData Z hZ K p s hs f hf).fiber_fst]
  exact ((RightHomotopyRel.factorsThroughLocalization C
    (kernelLiftData Z hZ K p s hs f hf).rightHomotopy).map_eq ((weakEquivalences C).Q)).symm

/-- The image retains the caller's entire original first leg in the actual ordinary Ho. -/
def chosenFiberHoImage {E B : C} (K : C) (p : E ⟶ B)
    (s : PullbackCone p (hZ.isInitial.to B)) :
    Set (((weakEquivalences C).Q).obj K ⟶ ((weakEquivalences C).Q).obj E) :=
  Set.range (fun f : ((weakEquivalences C).Q).obj K ⟶ ((weakEquivalences C).Q).obj s.pt =>
    f ≫ ((weakEquivalences C).Q).map s.fst)

/-- The actual null-fiber retains the original projection and caller's complete zero function. -/
def projectionHoNullFiber {E B : C} (K : C) (p : E ⟶ B) :
    Set (((weakEquivalences C).Q).obj K ⟶ ((weakEquivalences C).Q).obj E) :=
  {f | f ≫ ((weakEquivalences C).Q).map p = ((weakEquivalences C).Q).map (nullMap Z hZ K B)}

/-- Actual representative homotopy and covering homotopy prove the whole cofibrant image law. -/
theorem chosenFiberHoImage_eq_nullFiber {E B : C} (K : C) [IsCofibrant K]
    (p : E ⟶ B) [Fibration p] [IsFibrant B]
    (s : PullbackCone p (hZ.isInitial.to B)) (hs : IsLimit s) :
    chosenFiberHoImage Z hZ K p s = projectionHoNullFiber Z hZ K p := by
  let : IsFibrant E := isFibrant_of_fibration p
  let : IsFibrant s.pt := chosenFiber_isFibrant Z hZ p s hs
  apply Set.Subset.antisymm
  · rintro f ⟨g, rfl⟩
    obtain ⟨g, rfl⟩ := map_surjective_of_isLocalization ((weakEquivalences C).Q) K s.pt g
    change (((weakEquivalences C).Q).map g ≫ ((weakEquivalences C).Q).map s.fst) ≫
      ((weakEquivalences C).Q).map p = _
    rw [← ((weakEquivalences C).Q).map_comp, ← ((weakEquivalences C).Q).map_comp,
      chosenFiberMap_over_zero]
  · intro f hf
    obtain ⟨g, rfl⟩ := map_surjective_of_isLocalization ((weakEquivalences C).Q) K E f
    have hg : ((weakEquivalences C).Q).map (g ≫ p) = ((weakEquivalences C).Q).map
        (nullMap Z hZ K B) :=
      (((weakEquivalences C).Q).map_comp g p).trans hf
    exact ⟨((weakEquivalences C).Q).map (kernelLiftData Z hZ K p s hs g hg).fiberMap,
      kernelLiftData_ho_fac Z hZ K p s hs g hg⟩

/-- Actual replacement precomposition preserves the caller's whole zero function. -/
theorem replacementPrecomp_null {Kc K : C} (pK : Kc ⟶ K) [WeakEquivalence pK] (B : C) :
    QuillenOrdinaryHoReplacement.replacementPrecompEquiv pK B
        (((weakEquivalences C).Q).map (nullMap Z hZ K B)) =
      ((weakEquivalences C).Q).map (nullMap Z hZ Kc B) := by
  change ((weakEquivalences C).Q).map pK ≫ ((weakEquivalences C).Q).map (nullMap Z hZ K B) = _
  rw [← ((weakEquivalences C).Q).map_comp, nullMap_precomp]

/-- The full image property retains both actual replacement precomposition functions. -/
theorem replacementPrecomp_image_iff {Kc K E B : C}
    (pK : Kc ⟶ K) [WeakEquivalence pK] (p : E ⟶ B)
    (s : PullbackCone p (hZ.isInitial.to B))
    (f : ((weakEquivalences C).Q).obj K ⟶ ((weakEquivalences C).Q).obj E) :
    f ∈ chosenFiberHoImage Z hZ K p s ↔
      QuillenOrdinaryHoReplacement.replacementPrecompEquiv pK E f ∈
        chosenFiberHoImage Z hZ Kc p s := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨QuillenOrdinaryHoReplacement.replacementPrecompEquiv pK s.pt g, ?_⟩
    change QuillenOrdinaryHoReplacement.replacementPrecompEquiv pK s.pt g ≫
      ((weakEquivalences C).Q).map s.fst = QuillenOrdinaryHoReplacement.replacementPrecompEquiv pK
          E f
    change g ≫ ((weakEquivalences C).Q).map s.fst = f at hg
    rw [← QuillenOrdinaryHoReplacement.replacementPrecompEquiv_target, hg]
  · rintro ⟨g, hg⟩
    refine ⟨(QuillenOrdinaryHoReplacement.replacementPrecompEquiv pK s.pt).symm g, ?_⟩
    apply (QuillenOrdinaryHoReplacement.replacementPrecompEquiv pK E).injective
    change QuillenOrdinaryHoReplacement.replacementPrecompEquiv pK E
      ((QuillenOrdinaryHoReplacement.replacementPrecompEquiv pK s.pt).symm g ≫
        ((weakEquivalences C).Q).map s.fst) =
      QuillenOrdinaryHoReplacement.replacementPrecompEquiv pK E f
    rw [QuillenOrdinaryHoReplacement.replacementPrecompEquiv_target,
      Equiv.apply_symm_apply]
    exact hg

/-- The full null-fiber property retains the same actual replacement and original zero. -/
theorem replacementPrecomp_nullFiber_iff {Kc K E B : C}
    (pK : Kc ⟶ K) [WeakEquivalence pK] (p : E ⟶ B)
    (f : ((weakEquivalences C).Q).obj K ⟶ ((weakEquivalences C).Q).obj E) :
    f ∈ projectionHoNullFiber Z hZ K p ↔
      QuillenOrdinaryHoReplacement.replacementPrecompEquiv pK E f ∈
        projectionHoNullFiber Z hZ Kc p := by
  constructor
  · intro hf
    change _ ≫ ((weakEquivalences C).Q).map p = ((weakEquivalences C).Q).map (nullMap Z hZ Kc B)
    rw [← QuillenOrdinaryHoReplacement.replacementPrecompEquiv_target, hf,
      replacementPrecomp_null]
  · intro hf
    apply (QuillenOrdinaryHoReplacement.replacementPrecompEquiv pK B).injective
    rw [QuillenOrdinaryHoReplacement.replacementPrecompEquiv_target,
      replacementPrecomp_null]
    exact hf

/-- Model resolution proves chosen-fiber image/null-subset exactness for every coefficient. -/
theorem chosenFiberHoImage_eq_nullFiber_anyCoefficient {E B : C} (K : C)
    (p : E ⟶ B) [Fibration p] [IsFibrant B]
    (s : PullbackCone p (hZ.isInitial.to B)) (hs : IsLimit s) :
    chosenFiberHoImage Z hZ K p s = projectionHoNullFiber Z hZ K p := by
  let Kc := CofibrantObject.HoCat.resolutionObj K
  let pK : Kc ⟶ K := CofibrantObject.HoCat.pResolutionObj K
  let : IsCofibrant Kc := inferInstance
  let : WeakEquivalence pK := inferInstance
  apply Set.ext
  intro f
  rw [replacementPrecomp_image_iff Z hZ pK p s f,
    chosenFiberHoImage_eq_nullFiber Z hZ Kc p s hs,
    ← replacementPrecomp_nullFiber_iff Z hZ pK p f]

/-- Every entire ordinary Ho null-fiber arrow has a map into the same actual chosen fiber. -/
theorem chosenFiberHoImage_anyCoefficient_iff {E B : C} (K : C)
    (p : E ⟶ B) [Fibration p] [IsFibrant B]
    (s : PullbackCone p (hZ.isInitial.to B)) (hs : IsLimit s)
    (f : ((weakEquivalences C).Q).obj K ⟶ ((weakEquivalences C).Q).obj E) :
    (∃ g : ((weakEquivalences C).Q).obj K ⟶ ((weakEquivalences C).Q).obj s.pt,
      g ≫ ((weakEquivalences C).Q).map s.fst = f) ↔
      f ≫ ((weakEquivalences C).Q).map p = ((weakEquivalences C).Q).map (nullMap Z hZ K B) :=
  Set.ext_iff.mp (chosenFiberHoImage_eq_nullFiber_anyCoefficient Z hZ K p s hs) f

/-- A chosen lift of a Ho null map retains every coefficient and the caller's original inputs. -/
def chosenKernelHoLift {E B : C} (K : C) (p : E ⟶ B) [Fibration p] [IsFibrant B]
    (s : PullbackCone p (hZ.isInitial.to B)) (hs : IsLimit s)
    (f : {f : ((weakEquivalences C).Q).obj K ⟶ ((weakEquivalences C).Q).obj E |
      f ≫ ((weakEquivalences C).Q).map p = ((weakEquivalences C).Q).map (nullMap Z hZ K B)}) :
    ((weakEquivalences C).Q).obj K ⟶ ((weakEquivalences C).Q).obj s.pt :=
  Classical.choose ((chosenFiberHoImage_anyCoefficient_iff Z hZ K p s hs f.val).2 f.property)

/-- The full actual chosen lift reconstructs the original first-projection Ho arrow. -/
theorem chosenKernelHoLift_fac {E B : C} (K : C) (p : E ⟶ B) [Fibration p] [IsFibrant B]
    (s : PullbackCone p (hZ.isInitial.to B)) (hs : IsLimit s)
    (f : {f : ((weakEquivalences C).Q).obj K ⟶ ((weakEquivalences C).Q).obj E |
      f ≫ ((weakEquivalences C).Q).map p = ((weakEquivalences C).Q).map (nullMap Z hZ K B)}) :
    chosenKernelHoLift Z hZ K p s hs f ≫ ((weakEquivalences C).Q).map s.fst = f.val :=
  Classical.choose_spec ((chosenFiberHoImage_anyCoefficient_iff Z hZ K p s hs f.val).2 f.property)

/-- Both caller choices have the same whole first-leg image for every actual coefficient. -/
theorem chosenFiberHoImage_choice {E B : C} (K : C)
    (p : E ⟶ B) [Fibration p] [IsFibrant B]
    (s : PullbackCone p (hZ.isInitial.to B)) (hs : IsLimit s)
    (t : PullbackCone p (hZ.isInitial.to B)) (ht : IsLimit t) :
    chosenFiberHoImage Z hZ K p s = chosenFiberHoImage Z hZ K p t :=
  (chosenFiberHoImage_eq_nullFiber_anyCoefficient Z hZ K p s hs).trans
    (chosenFiberHoImage_eq_nullFiber_anyCoefficient Z hZ K p t ht).symm

end HomotopicalAlgebra.OrdinaryHoChosenFiberKernel
