/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Adjunction.RelativeProjectivity
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Tactic.Abel

/-!
# Comparison of relative resolutions

For a functor `U`, augmentation-splitting data on a target complex gives sections of its
kernel-factor maps after applying `U`. Termwise relative projectivity of the source constructs a
comparison lifting an endpoint morphism. Comparisons over the same augmentation morphism are chain
homotopic. The hypotheses are preadditivity, kernels in the source category, additivity of `U`,
and preservation of the displayed kernels.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe uC vC uD vD

namespace CategoryTheory.Functor

variable {D : Type uD} [Category.{vD} D] [Preadditive D] [HasZeroObject D] [HasKernels D]
  {C : Type uC} [Category.{vC} C] [Preadditive C]
  (U : D ⥤ C) [U.Additive]

/-- Restricted splitting operators of the chain augmentation. -/
structure AugmentationSplit (P : ChainComplex D ℕ) (Y : D)
    (β : P ⟶ (ChainComplex.single₀ D).obj Y) where
  /-- The restricted degree-zero augmentation section. -/
  section_ : U.obj Y ⟶ U.obj (P.X 0)
  /-- The restricted positive-degree split operators. -/
  s : ∀ n : ℕ, U.obj (P.X n) ⟶ U.obj (P.X (n + 1))
  /-- Section of the augmentation. -/
  section_comp : section_ ≫ U.map (β.f 0) = 𝟙 _
  /-- The augmented degree-zero split equation. -/
  zero : U.map (β.f 0) ≫ section_ + s 0 ≫ U.map (P.d 1 0) = 𝟙 _
  /-- The split equation in every positive degree. -/
  succ : ∀ n : ℕ,
    s (n + 1) ≫ U.map (P.d (n + 2) (n + 1)) +
      U.map (P.d (n + 1) n) ≫ s n = 𝟙 _

/-- A preserved kernel and split operators split the mapped kernel factor. -/
def splitKernelFactor (S : ShortComplex D)
    (s : U.obj S.X₂ ⟶ U.obj S.X₁) (r : U.obj S.X₃ ⟶ U.obj S.X₂)
    (h : s ≫ U.map S.f + U.map S.g ≫ r = 𝟙 _)
    [PreservesLimit (parallelPair S.g 0) U] :
    SplitEpi (U.map (kernel.lift S.g S.f S.zero)) := by
  let κ : Limits.kernel S.g ⟶ S.X₂ := kernel.ι S.g
  have hk : IsLimit (KernelFork.ofι (U.map κ)
      (show U.map κ ≫ U.map S.g = 0 by
        rw [← U.map_comp, kernel.condition, U.map_zero])) :=
    KernelFork.mapIsLimit (KernelFork.ofι κ (kernel.condition S.g)) (kernelIsKernel S.g) U
  let : Mono (U.map κ) := mono_of_isLimit_fork hk
  have hf : U.map (kernel.lift S.g S.f S.zero) ≫ U.map κ = U.map S.f := by
    rw [← U.map_comp, kernel.lift_ι]
  have hg : U.map κ ≫ U.map S.g = 0 := by
    rw [← U.map_comp, kernel.condition, U.map_zero]
  refine { section_ := U.map κ ≫ s, id := ?_ }
  apply (cancel_mono (U.map κ)).1
  simp only [Category.assoc, hf, Category.id_comp]
  have hz := congrArg (fun z : U.obj S.X₂ ⟶ U.obj S.X₂ => U.map κ ≫ z) h
  rw [Preadditive.comp_add, Category.comp_id] at hz
  have hr : U.map κ ≫ (U.map S.g ≫ r) = 0 := by
    rw [← Category.assoc, hg, Limits.zero_comp]
  rw [hr, add_zero] at hz
  exact hz

/-- Relative projectivity lifts an cycle through the incoming arrow. -/
def liftCycle {A : D} (hA : U.IsRelativeProjective A) (S : ShortComplex D)
    (s : U.obj S.X₂ ⟶ U.obj S.X₁) (r : U.obj S.X₃ ⟶ U.obj S.X₂)
    (h : s ≫ U.map S.f + U.map S.g ≫ r = 𝟙 _)
    [PreservesLimit (parallelPair S.g 0) U]
    (f : A ⟶ S.X₂) (hf : f ≫ S.g = 0) : A ⟶ S.X₁ :=
  Classical.choose (hA (kernel.lift S.g S.f S.zero)
    (splitKernelFactor U S s r h) (kernel.lift S.g f hf))

omit [HasZeroObject D] in
/-- The constructed relative cycle lift has the complete factorization equation. -/
theorem liftCycle_comp {A : D} (hA : U.IsRelativeProjective A) (S : ShortComplex D)
    (s : U.obj S.X₂ ⟶ U.obj S.X₁) (r : U.obj S.X₃ ⟶ U.obj S.X₂)
    (h : s ≫ U.map S.f + U.map S.g ≫ r = 𝟙 _)
    [PreservesLimit (parallelPair S.g 0) U]
    (f : A ⟶ S.X₂) (hf : f ≫ S.g = 0) :
    liftCycle U hA S s r h f hf ≫ S.f = f := by
  have hl := Classical.choose_spec (hA (kernel.lift S.g S.f S.zero)
    (splitKernelFactor U S s r h) (kernel.lift S.g f hf))
  have hi := congrArg (fun z : A ⟶ Limits.kernel S.g => z ≫ kernel.ι S.g) hl
  dsimp only [liftCycle]
  simpa only [Category.assoc, kernel.lift_ι] using hi

omit [HasKernels D] in
/-- Every augmentation chain map annihilates the incoming degree-one differential. -/
theorem augmentation_d {P : ChainComplex D ℕ} {Y : D}
    (β : P ⟶ (ChainComplex.single₀ D).obj Y) : P.d 1 0 ≫ β.f 0 = 0 := by
  have h := (β.comm 1 0).symm
  have hz : ((ChainComplex.single₀ D).obj Y).d 1 0 = 0 := rfl
  rw [hz, Limits.comp_zero] at h
  exact h

section Comparison

variable (Q P : ChainComplex D ℕ) (X Y : D)
  (α : Q ⟶ (ChainComplex.single₀ D).obj X)
  (β : P ⟶ (ChainComplex.single₀ D).obj Y)
  (σ : AugmentationSplit U P Y β)
  (hQ : ∀ n : ℕ, U.IsRelativeProjective (Q.X n))
  [PreservesLimit (parallelPair (β.f 0) 0) U]
  (hker : ∀ n : ℕ, PreservesLimit (parallelPair (P.d (n + 1) n) 0) U)

/-- The first comparison component uses the augmentation section. -/
def comparisonZero (f : X ⟶ Y) : Q.X 0 ⟶ P.X 0 :=
  Classical.choose (hQ 0 (β.f 0)
    { section_ := σ.section_, id := σ.section_comp } (α.f 0 ≫ f))

omit [HasKernels D] [U.Additive] [PreservesLimit (parallelPair (β.f 0) 0) U] in
/-- The endpoint map is retained in degree zero. -/
theorem comparisonZero_comp (f : X ⟶ Y) :
    comparisonZero U Q P X Y α β σ hQ f ≫ β.f 0 = α.f 0 ≫ f :=
  Classical.choose_spec (hQ 0 (β.f 0)
    { section_ := σ.section_, id := σ.section_comp } (α.f 0 ≫ f))

/-- Relative cycle lifting at the augmented degree-zero target. -/
def liftAtZero {A : D} (hA : U.IsRelativeProjective A)
    (z : A ⟶ P.X 0) (hz : z ≫ β.f 0 = 0) : A ⟶ P.X 1 :=
  liftCycle U hA (ShortComplex.mk (P.d 1 0) (β.f 0) (augmentation_d β))
    (σ.s 0) σ.section_ (by simpa only [add_comm] using σ.zero) z hz

/-- The augmented relative lift factors through the degree-one differential. -/
theorem liftAtZero_comp {A : D} (hA : U.IsRelativeProjective A)
    (z : A ⟶ P.X 0) (hz : z ≫ β.f 0 = 0) :
    liftAtZero U P Y β σ hA z hz ≫ P.d 1 0 = z :=
  liftCycle_comp U hA (ShortComplex.mk (P.d 1 0) (β.f 0) (augmentation_d β))
    (σ.s 0) σ.section_ (by simpa only [add_comm] using σ.zero) z hz

/-- Relative cycle lifting uses the target split operator at every positive degree. -/
def liftAtSucc (n : ℕ) {A : D} (hA : U.IsRelativeProjective A)
    (z : A ⟶ P.X (n + 1)) (hz : z ≫ P.d (n + 1) n = 0) : A ⟶ P.X (n + 2) := by
  let : PreservesLimit (parallelPair (P.d (n + 1) n) 0) U := hker n
  exact liftCycle U hA
    (ShortComplex.mk (P.d (n + 2) (n + 1)) (P.d (n + 1) n) (by simp))
    (σ.s (n + 1)) (σ.s n) (σ.succ n) z hz

omit [PreservesLimit (parallelPair (β.f 0) 0) U] in
/-- The positive relative lift factors through the same differential. -/
theorem liftAtSucc_comp (n : ℕ) {A : D} (hA : U.IsRelativeProjective A)
    (z : A ⟶ P.X (n + 1)) (hz : z ≫ P.d (n + 1) n = 0) :
    liftAtSucc U P Y β σ hker n hA z hz ≫ P.d (n + 2) (n + 1) = z := by
  let : PreservesLimit (parallelPair (P.d (n + 1) n) 0) U := hker n
  exact liftCycle_comp U hA
    (ShortComplex.mk (P.d (n + 2) (n + 1)) (P.d (n + 1) n) (by simp))
    (σ.s (n + 1)) (σ.s n) (σ.succ n) z hz

/-- The next comparison component is constructed by the first cycle. -/
def comparisonOne (f : X ⟶ Y) : Q.X 1 ⟶ P.X 1 :=
  liftAtZero U P Y β σ (hQ 1)
    (Q.d 1 0 ≫ comparisonZero U Q P X Y α β σ hQ f) (by
      let a : Q.X 0 ⟶ X := α.f 0
      have ha : Q.d 1 0 ≫ a = 0 := augmentation_d α
      have hc : Q.d 1 0 ≫ (a ≫ f) = 0 :=
        (Category.assoc _ _ _).symm.trans
          ((congrArg (fun z : Q.X 1 ⟶ X => z ≫ f) ha).trans (Limits.zero_comp (f := f)))
      have h0 : comparisonZero U Q P X Y α β σ hQ f ≫ β.f 0 = a ≫ f :=
        comparisonZero_comp U Q P X Y α β σ hQ f
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun z : Q.X 0 ⟶ Y => Q.d 1 0 ≫ z) h0).trans hc))

/-- The first chain square uses the same degree-zero comparison. -/
theorem comparisonOne_comp (f : X ⟶ Y) :
    comparisonOne U Q P X Y α β σ hQ f ≫ P.d 1 0 =
      Q.d 1 0 ≫ comparisonZero U Q P X Y α β σ hQ f :=
  liftAtZero_comp U P Y β σ (hQ 1) _ _

/-- Recursion step: the previous square makes the next target cycle. -/
def comparisonSucc (n : ℕ) (g : Q.X n ⟶ P.X n) (g' : Q.X (n + 1) ⟶ P.X (n + 1))
    (w : g' ≫ P.d (n + 1) n = Q.d (n + 1) n ≫ g) :
    Σ' g'' : Q.X (n + 2) ⟶ P.X (n + 2),
      g'' ≫ P.d (n + 2) (n + 1) = Q.d (n + 2) (n + 1) ≫ g' :=
  ⟨liftAtSucc U P Y β σ hker n (hQ (n + 2)) (Q.d (n + 2) (n + 1) ≫ g') (by
      rw [Category.assoc, w, ← Category.assoc, Q.d_comp_d, Limits.zero_comp]),
    liftAtSucc_comp U P Y β σ hker n (hQ (n + 2)) _ _⟩

/-- The chain comparison lifting the endpoint morphism. -/
def comparison (f : X ⟶ Y) : Q ⟶ P :=
  ChainComplex.mkHom Q P
    (comparisonZero U Q P X Y α β σ hQ f)
    (comparisonOne U Q P X Y α β σ hQ f)
    (comparisonOne_comp U Q P X Y α β σ hQ f)
    (fun n t => comparisonSucc U Q P Y β σ hQ hker n t.1 t.2.1 t.2.2)

/-- The full comparison retains the source and target augmentations. -/
@[reassoc]
theorem comparison_augmentation (f : X ⟶ Y) :
    comparison U Q P X Y α β σ hQ hker f ≫ β = α ≫ (ChainComplex.single₀ D).map f := by
  apply HomologicalComplex.to_single_hom_ext
  change (comparison U Q P X Y α β σ hQ hker f).f 0 ≫ β.f 0 =
    α.f 0 ≫ ((ChainComplex.single₀ D).map f).f 0
  rw [ChainComplex.single₀_map_f_zero]
  exact comparisonZero_comp U Q P X Y α β σ hQ f

/-- The first homotopy component lifts the zero-augmentation cycle. -/
def nullZero (e : Q ⟶ P) (he : e ≫ β = 0) : Q.X 0 ⟶ P.X 1 :=
  liftAtZero U P Y β σ (hQ 0) (e.f 0) (by
    have h := congrArg (fun z : Q ⟶ (ChainComplex.single₀ D).obj Y => z.f 0) he
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f_apply] using h)

/-- The first homotopy boundary is the map in degree zero. -/
theorem nullZero_comp (e : Q ⟶ P) (he : e ≫ β = 0) :
    nullZero U Q P Y β σ hQ e he ≫ P.d 1 0 = e.f 0 :=
  liftAtZero_comp U P Y β σ (hQ 0) _ _

/-- The next homotopy cycle is the map minus its boundary. -/
def nullOne (e : Q ⟶ P) (he : e ≫ β = 0) : Q.X 1 ⟶ P.X 2 :=
  liftAtSucc U P Y β σ hker 0 (hQ 1)
    (e.f 1 - Q.d 1 0 ≫ nullZero U Q P Y β σ hQ e he) (by
      rw [Preadditive.sub_comp, Category.assoc, e.comm, nullZero_comp, sub_self])

/-- The second homotopy boundary has the subtraction sign. -/
theorem nullOne_comp (e : Q ⟶ P) (he : e ≫ β = 0) :
    nullOne U Q P Y β σ hQ hker e he ≫ P.d 2 1 =
      e.f 1 - Q.d 1 0 ≫ nullZero U Q P Y β σ hQ e he :=
  liftAtSucc_comp U P Y β σ hker 0 (hQ 1) _ _

/-- The recursive homotopy component is lifted from its remaining cycle. -/
def nullSucc (e : Q ⟶ P) (n : ℕ) (g : Q.X n ⟶ P.X (n + 1))
    (g' : Q.X (n + 1) ⟶ P.X (n + 2))
    (w : e.f (n + 1) = Q.d (n + 1) n ≫ g + g' ≫ P.d (n + 2) (n + 1)) :
    Σ' g'' : Q.X (n + 2) ⟶ P.X (n + 3),
      e.f (n + 2) = Q.d (n + 2) (n + 1) ≫ g' + g'' ≫ P.d (n + 3) (n + 2) := by
  let z := e.f (n + 2) - Q.d (n + 2) (n + 1) ≫ g'
  have hz : z ≫ P.d (n + 2) (n + 1) = 0 := by
    dsimp only [z]
    rw [Preadditive.sub_comp, Category.assoc, e.comm, w, Preadditive.comp_add,
      ← Category.assoc, Q.d_comp_d, Limits.zero_comp, zero_add, sub_self]
  refine ⟨liftAtSucc U P Y β σ hker (n + 1) (hQ (n + 2)) z hz, ?_⟩
  rw [liftAtSucc_comp]
  dsimp only [z]
  abel

/-- Inductive construction gives a homotopy for each zero-augmentation chain map. -/
def nullHomotopy (e : Q ⟶ P) (he : e ≫ β = 0) : Homotopy e 0 :=
  Homotopy.mkInductive e
    (nullZero U Q P Y β σ hQ e he)
    (nullZero_comp U Q P Y β σ hQ e he).symm
    (nullOne U Q P Y β σ hQ hker e he)
    (by rw [nullOne_comp]; abel)
    (fun n t => nullSucc U Q P Y β σ hQ hker e n t.1 t.2.1 t.2.2)

/-- Any two comparisons over the same endpoint map are homotopic. -/
def comparisonHomotopy (f : X ⟶ Y) (g h : Q ⟶ P)
    (hg : g ≫ β = α ≫ (ChainComplex.single₀ D).map f)
    (hh : h ≫ β = α ≫ (ChainComplex.single₀ D).map f) : Homotopy g h :=
  Homotopy.equivSubZero.invFun (nullHomotopy U Q P Y β σ hQ hker (g - h) (by
    rw [Preadditive.sub_comp, hg, hh, sub_self]))

end Comparison
end CategoryTheory.Functor
