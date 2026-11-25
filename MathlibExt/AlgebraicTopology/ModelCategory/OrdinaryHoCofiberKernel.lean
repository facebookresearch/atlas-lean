/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyCategory
import Mathlib.AlgebraicTopology.ModelCategory.RightHomotopy
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# Actual ordinary homotopy cofiber kernels

The canonical ordinary homotopy category is used throughout. Homotopy
extension along the actual cofibration strictifies a null restriction.
The given pushout cocone then supplies its original desc function.
A contractible actual cone gives the first cofiber kernel law as well.
Every chosen cocone and both legs remain explicit. No preservation of
pushouts by the ordinary homotopy category is used.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped ZeroObject

namespace HomotopicalAlgebra.OrdinaryHoCofiberKernel

variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasZeroObject C]

/-- The actual two zero-object endpoint maps, in their original order. -/
def nullMap (X Y : C) : X ⟶ Y :=
  HasZeroObject.zeroIsTerminal.from X ≫ HasZeroObject.zeroIsInitial.to Y

/-- The null class is the image of those two actual endpoint maps. -/
def nullHom (X Y : C) :
    ((weakEquivalences C).Q).obj X ⟶ ((weakEquivalences C).Q).obj Y :=
  ((weakEquivalences C).Q).map (nullMap X Y)

omit [ModelCategory C] in
/-- Every actual source map retains the same terminal zero endpoint. -/
theorem precomp_nullMap {X Y Z : C} (f : X ⟶ Y) :
    f ≫ nullMap Y Z = nullMap X Z := by
  unfold nullMap
  rw [← Category.assoc]
  exact congrArg (fun q => q ≫ HasZeroObject.zeroIsInitial.to Z)
    (HasZeroObject.zeroIsTerminal.hom_ext _ _)

omit [ModelCategory C] in
/-- Every actual target map retains the same initial zero endpoint. -/
theorem nullMap_postcomp {X Y Z : C} (g : Y ⟶ Z) :
    nullMap X Y ≫ g = nullMap X Z := by
  unfold nullMap
  rw [Category.assoc]
  exact congrArg (fun q => HasZeroObject.zeroIsTerminal.from X ≫ q)
    (HasZeroObject.zeroIsInitial.hom_ext _ _)

/-- The entire actual source function preserves its null class. -/
theorem precomp_nullHom {X Y Z : C} (f : X ⟶ Y) :
    ((weakEquivalences C).Q).map f ≫ nullHom Y Z = nullHom X Z := by
  rw [nullHom, ← Functor.map_comp, precomp_nullMap]
  rfl

/-- The entire actual target function preserves its null class. -/
theorem nullHom_postcomp_map {X Y Z : C} (g : Y ⟶ Z) :
    nullHom X Y ≫ ((weakEquivalences C).Q).map g = nullHom X Z := by
  rw [nullHom, ← Functor.map_comp, nullMap_postcomp]
  rfl

private theorem zero_cofibrant : IsCofibrant (0 : C) := by
  rw [isCofibrant_iff_of_isInitial (𝟙 (0 : C)) HasZeroObject.zeroIsInitial]
  infer_instance

/-- Actual ordinary Hom out of zero is unique, by the fundamental lemma. -/
theorem subsingleton_hom_from_zero (E : C) [IsFibrant E] :
    Subsingleton (((weakEquivalences C).Q).obj (0 : C) ⟶
      ((weakEquivalences C).Q).obj E) := by
  let _ : IsCofibrant (0 : C) := zero_cofibrant
  refine ⟨fun a b => ?_⟩
  obtain ⟨f, rfl⟩ := map_surjective_of_isLocalization
    ((weakEquivalences C).Q) (0 : C) E a
  obtain ⟨g, rfl⟩ := map_surjective_of_isLocalization
    ((weakEquivalences C).Q) (0 : C) E b
  exact ((weakEquivalences C).Q).congr_map (HasZeroObject.zeroIsInitial.hom_ext f g)

/-- Every full target Ho morphism preserves the original null class. -/
theorem nullHom_postcomp {X Y E : C} [IsFibrant E]
    (g : ((weakEquivalences C).Q).obj Y ⟶ ((weakEquivalences C).Q).obj E) :
    nullHom X Y ≫ g = nullHom X E := by
  have h := subsingleton_hom_from_zero E
  change ((weakEquivalences C).Q).map
      (HasZeroObject.zeroIsTerminal.from X ≫ HasZeroObject.zeroIsInitial.to Y) ≫ g =
    ((weakEquivalences C).Q).map
      (HasZeroObject.zeroIsTerminal.from X ≫ HasZeroObject.zeroIsInitial.to E)
  rw [Functor.map_comp, Functor.map_comp, Category.assoc]
  exact congrArg (fun q => ((weakEquivalences C).Q).map
    (HasZeroObject.zeroIsTerminal.from X) ≫ q) (h.elim _ _)

/-- A genuinely weak contraction makes all actual ordinary target Hom classes null. -/
theorem subsingleton_hom_of_weak_contraction (W E : C) [IsFibrant E]
    (hW : weakEquivalences C (HasZeroObject.zeroIsTerminal.from W)) :
    Subsingleton (((weakEquivalences C).Q).obj W ⟶ ((weakEquivalences C).Q).obj E) := by
  let q := ((weakEquivalences C).Q).map (HasZeroObject.zeroIsTerminal.from W)
  let _ : IsIso q := Localization.inverts ((weakEquivalences C).Q)
    (weakEquivalences C) _ hW
  have h := subsingleton_hom_from_zero E
  refine ⟨fun a b => ?_⟩
  exact (cancel_epi (inv q)).mp (h.elim (inv q ≫ a) (inv q ≫ b))

/-- The kernel retains the whole original source map and the literal null endpoint class. -/
def HomKernel {X Y : C} (f : X ⟶ Y) (E : C) :=
  {g : ((weakEquivalences C).Q).obj Y ⟶ ((weakEquivalences C).Q).obj E //
    ((weakEquivalences C).Q).map f ≫ g = nullHom X E}

/-- Every original Arrow square induces the actual contravariant kernel function. -/
def kernelSourceMap {F G : Arrow C} (q : F ⟶ G) (E : C) :
    HomKernel G.hom E → HomKernel F.hom E :=
  fun g => ⟨((weakEquivalences C).Q).map q.right ≫ g.1, by
    rw [← Category.assoc, ← Functor.map_comp, ← q.w,
      Functor.map_comp, Category.assoc, g.2, precomp_nullHom]⟩

/-- Every entire target map induces the actual covariant kernel function. -/
def kernelTargetMap {X Y E E' : C} (f : X ⟶ Y) (p : E ⟶ E') :
    HomKernel f E → HomKernel f E' :=
  fun g => ⟨g.1 ≫ ((weakEquivalences C).Q).map p, by
    rw [← Category.assoc, g.2, nullHom_postcomp_map]⟩

/-- The complete original source Arrow acts on each full kernel morphism. -/
theorem kernelSourceMap_value {F G : Arrow C} (q : F ⟶ G) (E : C)
    (g : HomKernel G.hom E) :
    (kernelSourceMap q E g).1 = ((weakEquivalences C).Q).map q.right ≫ g.1 := rfl

/-- The complete target function retains the same actual ordinary Ho composition. -/
theorem kernelTargetMap_value {X Y E E' : C} (f : X ⟶ Y) (p : E ⟶ E')
    (g : HomKernel f E) :
    (kernelTargetMap f p g).1 = g.1 ≫ ((weakEquivalences C).Q).map p := rfl

/-- All actual source identities retain the entire identity kernel function. -/
theorem kernelSourceMap_id (F : Arrow C) (E : C) :
    kernelSourceMap (𝟙 F) E = id := by
  funext g
  apply Subtype.ext
  change ((weakEquivalences C).Q).map (𝟙 F.right) ≫ g.1 = g.1
  rw [((weakEquivalences C).Q).map_id, Category.id_comp]

/-- The complete actual source kernel functions compose in their original variance. -/
theorem kernelSourceMap_comp {F G H : Arrow C} (q : F ⟶ G) (r : G ⟶ H) (E : C) :
    kernelSourceMap (q ≫ r) E = kernelSourceMap q E ∘ kernelSourceMap r E := by
  funext g
  apply Subtype.ext
  simp only [kernelSourceMap, Arrow.comp_right, Functor.map_comp, Category.assoc,
    Function.comp_apply]

/-- All actual target identities retain the entire identity kernel function. -/
theorem kernelTargetMap_id {X Y : C} (f : X ⟶ Y) (E : C) :
    kernelTargetMap f (𝟙 E) = id := by
  funext g
  apply Subtype.ext
  change g.1 ≫ ((weakEquivalences C).Q).map (𝟙 E) = g.1
  rw [((weakEquivalences C).Q).map_id, Category.comp_id]

/-- Both complete target kernel functions compose on every original source map. -/
theorem kernelTargetMap_comp {X Y E E' E'' : C} (f : X ⟶ Y)
    (p : E ⟶ E') (r : E' ⟶ E'') :
    kernelTargetMap f (p ≫ r) = kernelTargetMap f r ∘ kernelTargetMap f p := by
  funext g
  apply Subtype.ext
  simp only [kernelTargetMap, Functor.map_comp, Category.assoc, Function.comp_apply]

/-- The complete source and target actions commute on the same kernel classes. -/
theorem kernelSourceMap_target {F G : Arrow C} (q : F ⟶ G) {E E' : C}
    (p : E ⟶ E') :
    kernelSourceMap q E' ∘ kernelTargetMap G.hom p =
      kernelTargetMap F.hom p ∘ kernelSourceMap q E := by
  funext g
  apply Subtype.ext
  change ((weakEquivalences C).Q).map q.right ≫ (g.1 ≫ ((weakEquivalences C).Q).map p) =
    (((weakEquivalences C).Q).map q.right ≫ g.1) ≫ ((weakEquivalences C).Q).map p
  exact (Category.assoc _ _ _).symm

/-- A null restriction has an actual good-path extension along its original cofibration. -/
theorem nullification_of_map_eq {X Y E : C} [IsCofibrant X] [IsFibrant E]
    (i : X ⟶ Y) [Cofibration i]
    (g : ((weakEquivalences C).Q).obj Y ⟶ ((weakEquivalences C).Q).obj E)
    (hg : ((weakEquivalences C).Q).map i ≫ g = nullHom X E) :
    ∃ (g₀ g₁ : Y ⟶ E) (P : PathObject E) (H : P.RightHomotopy g₀ g₁),
      P.IsGood ∧ ((weakEquivalences C).Q).map g₀ = g ∧ i ≫ g₁ = nullMap X E ∧
        H.h ≫ P.p₀ = g₀ ∧ H.h ≫ P.p₁ = g₁ := by
  let _ : IsCofibrant Y := isCofibrant_of_cofibration i
  obtain ⟨g₀, hg₀⟩ := map_surjective_of_isLocalization ((weakEquivalences C).Q) Y E g
  have hRel : RightHomotopyRel (i ≫ g₀) (nullMap X E) := by
    rw [RightHomotopyRel.iff_map_eq ((weakEquivalences C).Q)]
    rw [Functor.map_comp, hg₀]
    exact hg
  obtain ⟨P, hP, ⟨H⟩⟩ := hRel.exists_good_pathObject
  let _ : P.IsGood := hP
  obtain ⟨g₁, H₁, hCompatible⟩ := H.homotopy_extension i g₀ rfl
  have hRestriction : i ≫ g₁ = nullMap X E := by
    calc
      i ≫ g₁ = i ≫ (H₁.h ≫ P.p₁) := by rw [H₁.h₁]
      _ = (i ≫ H₁.h) ≫ P.p₁ := (Category.assoc _ _ _).symm
      _ = H.h ≫ P.p₁ := congrArg (fun q => q ≫ P.p₁) hCompatible
      _ = nullMap X E := H.h₁
  exact ⟨g₀, g₁, P, H₁, hP, hg₀, hRestriction, H₁.h₀, H₁.h₁⟩

/-- The SAME actual chosen quotient pushout has precisely the null-restriction image in Ho. -/
theorem chosen_quotient_image_iff {X Y E : C} [IsCofibrant X] [IsFibrant E]
    (i : X ⟶ Y) [Cofibration i]
    (c : PushoutCocone i (HasZeroObject.zeroIsTerminal.from X)) (hc : IsColimit c)
    (g : ((weakEquivalences C).Q).obj Y ⟶ ((weakEquivalences C).Q).obj E) :
    (∃ h : ((weakEquivalences C).Q).obj c.pt ⟶ ((weakEquivalences C).Q).obj E,
      ((weakEquivalences C).Q).map c.inl ≫ h = g) ↔
      ((weakEquivalences C).Q).map i ≫ g = nullHom X E := by
  constructor
  · rintro ⟨h, rfl⟩
    have hZero := subsingleton_hom_from_zero E
    calc
      ((weakEquivalences C).Q).map i ≫ (((weakEquivalences C).Q).map c.inl ≫ h) =
          ((weakEquivalences C).Q).map (i ≫ c.inl) ≫ h := by
        rw [Functor.map_comp, Category.assoc]
      _ = ((weakEquivalences C).Q).map
          (HasZeroObject.zeroIsTerminal.from X ≫ c.inr) ≫ h :=
        congrArg (fun q => ((weakEquivalences C).Q).map q ≫ h) c.condition
      _ = nullHom X E := by
        rw [Functor.map_comp, Category.assoc]
        change ((weakEquivalences C).Q).map (HasZeroObject.zeroIsTerminal.from X) ≫
          (((weakEquivalences C).Q).map c.inr ≫ h) =
          ((weakEquivalences C).Q).map (nullMap X E)
        rw [nullMap, Functor.map_comp]
        exact congrArg (fun q => ((weakEquivalences C).Q).map
          (HasZeroObject.zeroIsTerminal.from X) ≫ q) (hZero.elim _ _)
  · intro hg
    let _ : IsCofibrant Y := isCofibrant_of_cofibration i
    obtain ⟨g₀, g₁, P, H, _, hg₀, hi, _, _⟩ := nullification_of_map_eq i g hg
    let h := PushoutCocone.IsColimit.desc hc g₁ (HasZeroObject.zeroIsInitial.to E) hi
    have hLeg : c.inl ≫ h = g₁ := PushoutCocone.IsColimit.inl_desc hc _ _ hi
    have hSame : ((weakEquivalences C).Q).map g₁ = g := by
      have hHo := (RightHomotopyRel.iff_map_eq ((weakEquivalences C).Q) Y E).mp
        H.rightHomotopyRel
      exact hHo.symm.trans hg₀
    refine ⟨((weakEquivalences C).Q).map h, ?_⟩
    rw [← Functor.map_comp, hLeg]
    exact hSame

/-- The first cone-cofiber image law uses the actual weak cone contraction. -/
theorem chosen_cone_cofiber_image_iff {X Y W E : C}
    [IsCofibrant X] [IsCofibrant Y] [IsFibrant E]
    (i : X ⟶ W) [Cofibration i]
    (hW : weakEquivalences C (HasZeroObject.zeroIsTerminal.from W))
    (f : X ⟶ Y) (c : PushoutCocone i f) (hc : IsColimit c)
    (g : ((weakEquivalences C).Q).obj Y ⟶ ((weakEquivalences C).Q).obj E) :
    (∃ h : ((weakEquivalences C).Q).obj c.pt ⟶ ((weakEquivalences C).Q).obj E,
      ((weakEquivalences C).Q).map c.inr ≫ h = g) ↔
      ((weakEquivalences C).Q).map f ≫ g = nullHom X E := by
  constructor
  · rintro ⟨h, rfl⟩
    have hCone := subsingleton_hom_of_weak_contraction W E hW
    calc
      ((weakEquivalences C).Q).map f ≫ (((weakEquivalences C).Q).map c.inr ≫ h) =
          ((weakEquivalences C).Q).map (f ≫ c.inr) ≫ h := by
        rw [Functor.map_comp, Category.assoc]
      _ = ((weakEquivalences C).Q).map (i ≫ c.inl) ≫ h :=
        congrArg (fun q => ((weakEquivalences C).Q).map q ≫ h) c.condition.symm
      _ = nullHom X E := by
        rw [Functor.map_comp, Category.assoc,
          hCone.elim (((weakEquivalences C).Q).map c.inl ≫ h) (nullHom W E),
          precomp_nullHom]
  · intro hg
    obtain ⟨g₀, hg₀⟩ := map_surjective_of_isLocalization ((weakEquivalences C).Q) Y E g
    have hRel : RightHomotopyRel (nullMap X E) (f ≫ g₀) := by
      rw [RightHomotopyRel.iff_map_eq ((weakEquivalences C).Q), Functor.map_comp, hg₀]
      exact hg.symm
    obtain ⟨P, hP, ⟨H⟩⟩ := hRel.exists_good_pathObject
    let _ : P.IsGood := hP
    obtain ⟨u, Hu, hCompatible⟩ := H.homotopy_extension i (nullMap W E)
      (precomp_nullMap i)
    have hi : i ≫ u = f ≫ g₀ := by
      calc
        i ≫ u = i ≫ (Hu.h ≫ P.p₁) := by rw [Hu.h₁]
        _ = (i ≫ Hu.h) ≫ P.p₁ := (Category.assoc _ _ _).symm
        _ = H.h ≫ P.p₁ := congrArg (fun q => q ≫ P.p₁) hCompatible
        _ = f ≫ g₀ := H.h₁
    let h := PushoutCocone.IsColimit.desc hc u g₀ hi
    have hLeg : c.inr ≫ h = g₀ := PushoutCocone.IsColimit.inr_desc hc _ _ hi
    refine ⟨((weakEquivalences C).Q).map h, ?_⟩
    rw [← Functor.map_comp, hLeg]
    exact hg₀

omit [HasZeroObject C] in
/-- Both actual target-side functions commute on each complete chosen cofiber. -/
theorem cofiber_restriction_target {X Y W E E' : C} (i : X ⟶ W) (f : X ⟶ Y)
    (c : PushoutCocone i f) (p : E ⟶ E')
    (h : ((weakEquivalences C).Q).obj c.pt ⟶ ((weakEquivalences C).Q).obj E) :
    ((weakEquivalences C).Q).map c.inr ≫ (h ≫ ((weakEquivalences C).Q).map p) =
      (((weakEquivalences C).Q).map c.inr ≫ h) ≫ ((weakEquivalences C).Q).map p :=
  (Category.assoc _ _ _).symm

omit [HasZeroObject C] in
/-- A genuine whole cofiber map retains the actual source-Arrow restriction square. -/
theorem cofiber_restriction_source {F G : Arrow C} {W W' E : C}
    (i : F.left ⟶ W) (j : G.left ⟶ W')
    (c : PushoutCocone i F.hom) (d : PushoutCocone j G.hom)
    (q : F ⟶ G) (k : c.pt ⟶ d.pt)
    (hk : c.inr ≫ k = q.right ≫ d.inr)
    (h : ((weakEquivalences C).Q).obj d.pt ⟶ ((weakEquivalences C).Q).obj E) :
    ((weakEquivalences C).Q).map c.inr ≫ (((weakEquivalences C).Q).map k ≫ h) =
      ((weakEquivalences C).Q).map q.right ≫
        (((weakEquivalences C).Q).map d.inr ≫ h) := by
  rw [← Category.assoc, ← Functor.map_comp, hk, Functor.map_comp, Category.assoc]

end HomotopicalAlgebra.OrdinaryHoCofiberKernel
