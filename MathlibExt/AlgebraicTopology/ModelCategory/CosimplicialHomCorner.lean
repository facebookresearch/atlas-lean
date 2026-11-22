/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.FiniteResolutionTensor
public import MathlibExt.AlgebraicTopology.ModelCategory.Reedy
public import MathlibExt.CategoryTheory.Reedy.FiniteBoundaries
public import Mathlib.AlgebraicTopology.ModelCategory.Transport
public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

public import MathlibExt.CategoryTheory.ComposableArrows.Arrow

/-!
# The actual relative cosimplicial Hom corner

The corner uses the unchanged source transformation and coefficient arrow.
Its target is the original simplicial pullback in the specified factor order.
The same corner is ordinary left Hom in the arrow category followed by the
actual identity-to-arrow comparison. All projections and simplex operators
retain their original coefficient maps.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits
open scoped Simplicial

namespace HomotopicalAlgebra.CosimplicialHomCorner

variable {C : Type u} [Category.{v} C]

/-- The actual left resolution Hom at the original coefficient object. -/
abbrev hom (A : CosimplicialObject C) (X : C) := ResolutionHomComplex.left A X

/-- The same whole cosimplicial transformation gives the source action in every degree. -/
abbrev precomp {A B : CosimplicialObject C} (h : A ⟶ B) (X : C) : hom B X ⟶ hom A X :=
  ResolutionHomComplex.precomp h ((SimplicialObject.const C).obj X)

/-- The same original coefficient arrow gives the target action in every degree. -/
abbrev postcomp (A : CosimplicialObject C) {X Y : C} (p : X ⟶ Y) : hom A X ⟶ hom A Y :=
  ResolutionHomComplex.postcomp A ((SimplicialObject.const C).map p)

/-- The original simplicial pullback keeps Hom(A,X) first and Hom(B,Y) second. -/
abbrev target {A B : CosimplicialObject C} (h : A ⟶ B) {X Y : C} (p : X ⟶ Y) :=
  pullback (postcomp A p) (precomp h Y)

/-- The original relative mapping arrow is its actual full pullback lift. -/
def map {A B : CosimplicialObject C} (h : A ⟶ B) {X Y : C} (p : X ⟶ Y) : hom B X ⟶ target h p :=
  pullback.lift (precomp h X) (postcomp B p)
    (ResolutionHomComplex.precomp_postcomp h ((SimplicialObject.const C).map p))

/-- The first projection retains the entire original source precomposition. -/
@[reassoc]
theorem map_fst {A B : CosimplicialObject C} (h : A ⟶ B) {X Y : C} (p : X ⟶ Y) :
    map h p ≫ pullback.fst (postcomp A p) (precomp h Y) = precomp h X := pullback.lift_fst _ _ _

/-- The second projection retains the entire original coefficient postcomposition. -/
@[reassoc]
theorem map_snd {A B : CosimplicialObject C} (h : A ⟶ B) {X Y : C} (p : X ⟶ Y) :
    map h p ≫ pullback.snd (postcomp A p) (precomp h Y) = postcomp B p := pullback.lift_snd _ _ _

/-- Every original source degree and structure square is retained as an actual arrow diagram. -/
def arrowDiagram {A B : CosimplicialObject C} (h : A ⟶ B) : CosimplicialObject (Arrow C) where
  obj n := Arrow.mk (h.app n)
  map {n m} f := Arrow.homMk (A.map f) (B.map f) (h.naturality f)
  map_id n := by
    apply Arrow.hom_ext
    · exact A.map_id n
    · exact B.map_id n
  map_comp f g := by
    apply Arrow.hom_ext
    · exact A.map_comp f g
    · exact B.map_comp f g

/-- Every original identity coefficient has its actual identity-arrow presentation. -/
abbrev identityArrow (X : C) : Arrow C := Arrow.mk (𝟙 X)

/-- The whole identity-to-arrow map keeps the original p as its target component. -/
def identityToArrow {X Y : C} (p : X ⟶ Y) : identityArrow X ⟶ Arrow.mk p :=
  Arrow.homMk (𝟙 X) p (by simp)

/-- The entire coefficient arrow square has its original source projection in left Hom. -/
def arrowFst {A B : CosimplicialObject C} (h : A ⟶ B) {X Y : C} (p : X ⟶ Y) :
    ResolutionHomComplex.left (arrowDiagram h) (Arrow.mk p) ⟶ hom A X where
  app n := ↾fun f => f.left
  naturality {n m} g := by
    ext f
    change Arrow.mk (h.app n.unop) ⟶ Arrow.mk p at f
    exact (congrArg Arrow.Hom.left
      (ResolutionHomComplex.left_map_apply (arrowDiagram h) (Arrow.mk p) g f)).trans
        (ResolutionHomComplex.left_map_apply A X g f.left).symm

/-- The entire coefficient arrow square has its original target projection in left Hom. -/
def arrowSnd {A B : CosimplicialObject C} (h : A ⟶ B) {X Y : C} (p : X ⟶ Y) :
    ResolutionHomComplex.left (arrowDiagram h) (Arrow.mk p) ⟶ hom B Y where
  app n := ↾fun f => f.right
  naturality {n m} g := by
    ext f
    change Arrow.mk (h.app n.unop) ⟶ Arrow.mk p at f
    exact (congrArg Arrow.Hom.right
      (ResolutionHomComplex.left_map_apply (arrowDiagram h) (Arrow.mk p) g f)).trans
        (ResolutionHomComplex.left_map_apply B Y g f.right).symm

/-- The actual arrow-Hom projections retain their original whole commuting coefficient square. -/
theorem arrow_projection_square {A B : CosimplicialObject C} (h : A ⟶ B) {X Y : C} (p : X ⟶ Y) :
    arrowFst h p ≫ postcomp A p = arrowSnd h p ≫ precomp h Y := by
  ext n f
  change Arrow.mk (h.app n.unop) ⟶ Arrow.mk p at f
  exact f.w

/-- Every supplied whole pair of source/target maps gives the original full arrow-Hom map. -/
def arrowLift {A B : CosimplicialObject C} (h : A ⟶ B) {X Y : C} (p : X ⟶ Y)
    {K : SSet.{v}} (a : K ⟶ hom A X) (b : K ⟶ hom B Y)
    (w : a ≫ postcomp A p = b ≫ precomp h Y) :
    K ⟶ ResolutionHomComplex.left (arrowDiagram h) (Arrow.mk p) where
  app n := ↾fun k => Arrow.homMk (a.app n k) (b.app n k) (by
    have hw := congrArg (fun t => t.app n k) w
    exact hw)
  naturality {n m} f := by
    ext k
    apply Arrow.hom_ext
    · exact a.naturality_apply f k
    · exact b.naturality_apply f k

/-- The first original arrow lift projection is exactly the supplied original map. -/
@[reassoc]
theorem arrowLift_fst {A B : CosimplicialObject C} (h : A ⟶ B) {X Y : C} (p : X ⟶ Y)
    {K : SSet.{v}} (a : K ⟶ hom A X) (b : K ⟶ hom B Y)
    (w : a ≫ postcomp A p = b ≫ precomp h Y) : arrowLift h p a b w ≫ arrowFst h p = a := by
  ext n k
  rfl

/-- The second original arrow lift projection is exactly the supplied original map. -/
@[reassoc]
theorem arrowLift_snd {A B : CosimplicialObject C} (h : A ⟶ B) {X Y : C} (p : X ⟶ Y)
    {K : SSet.{v}} (a : K ⟶ hom A X) (b : K ⟶ hom B Y)
    (w : a ≫ postcomp A p = b ≫ precomp h Y) : arrowLift h p a b w ≫ arrowSnd h p = b := by
  ext n k
  rfl

/-- The full original arrow Hom is the original simplicial pullback by its actual universal property. -/
theorem arrowIsPullback {A B : CosimplicialObject C} (h : A ⟶ B) {X Y : C} (p : X ⟶ Y) :
    IsPullback (arrowFst h p) (arrowSnd h p) (postcomp A p) (precomp h Y) :=
  IsPullback.of_isLimit
    (PullbackCone.IsLimit.mk
      (arrow_projection_square h p)
      (fun s => arrowLift h p s.fst s.snd s.condition)
      (fun s => arrowLift_fst h p _ _ _)
      (fun s => arrowLift_snd h p _ _ _)
      (by
        intro s m hm₁ hm₂
        ext n k
        apply Arrow.hom_ext
        · exact congrArg (fun t => t.app n k) hm₁
        · exact congrArg (fun t => t.app n k) hm₂))

/-- The actual original arrow Hom has the full original target pullback isomorphism. -/
def targetArrowIso {A B : CosimplicialObject C} (h : A ⟶ B) {X Y : C} (p : X ⟶ Y) :
    ResolutionHomComplex.left (arrowDiagram h) (Arrow.mk p) ≅ target h p :=
  (arrowIsPullback h p).isoPullback

/-- The original pullback comparison retains its whole first projection. -/
@[reassoc]
theorem targetArrowIso_hom_fst {A B : CosimplicialObject C} (h : A ⟶ B)
    {X Y : C} (p : X ⟶ Y) :
    (targetArrowIso h p).hom ≫ pullback.fst (postcomp A p) (precomp h Y) = arrowFst h p :=
  (arrowIsPullback h p).isoPullback_hom_fst

/-- The original pullback comparison retains its whole second projection. -/
@[reassoc]
theorem targetArrowIso_hom_snd {A B : CosimplicialObject C} (h : A ⟶ B)
    {X Y : C} (p : X ⟶ Y) :
    (targetArrowIso h p).hom ≫ pullback.snd (postcomp A p) (precomp h Y) = arrowSnd h p :=
  (arrowIsPullback h p).isoPullback_hom_snd

/-- The original Hom(B,X) is exactly the entire Hom of the source arrow into the identity arrow. -/
def sourceArrowIso {A B : CosimplicialObject C} (h : A ⟶ B) (X : C) :
    hom B X ≅ ResolutionHomComplex.left (arrowDiagram h) (identityArrow X) where
  hom := arrowLift h (𝟙 X) (precomp h X) (𝟙 _) (by
    ext n f
    change (h.app n.unop ≫ f) ≫ 𝟙 X = h.app n.unop ≫ f
    exact Category.comp_id _)
  inv := arrowSnd h (𝟙 X)
  hom_inv_id := arrowLift_snd h (𝟙 X) _ _ _
  inv_hom_id := by
    ext n f
    change Arrow.mk (h.app n.unop) ⟶ Arrow.mk (𝟙 X) at f
    apply Arrow.hom_ext
    · exact f.w.symm.trans (Category.comp_id _)
    · rfl

/-- The forward source comparison retains the same full original source coefficient. -/
theorem sourceArrowIso_hom_left {A B : CosimplicialObject C} (h : A ⟶ B) (X : C)
    (n : SimplexCategoryᵒᵖ) (f : B.obj n.unop ⟶ X) :
    ((sourceArrowIso h X).hom.app n f).left = h.app n.unop ≫ f := rfl

/-- The forward source comparison retains the same full original target coefficient. -/
theorem sourceArrowIso_hom_right {A B : CosimplicialObject C} (h : A ⟶ B) (X : C)
    (n : SimplexCategoryᵒᵖ) (f : B.obj n.unop ⟶ X) :
    ((sourceArrowIso h X).hom.app n f).right = f := rfl

/-- The complete original corner is ordinary left-Hom postcomposition of the same arrow frame. -/
theorem arrow_postcomp_eq_map {A B : CosimplicialObject C} (h : A ⟶ B)
    {X Y : C} (p : X ⟶ Y) :
    (sourceArrowIso h X).hom ≫ postcomp (arrowDiagram h) (identityToArrow p) ≫
      (targetArrowIso h p).hom = map h p := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, targetArrowIso_hom_fst, map_fst]
    ext n f
    change (h.app n.unop ≫ f) ≫ 𝟙 X = h.app n.unop ≫ f
    exact Category.comp_id _
  · rw [Category.assoc, Category.assoc, targetArrowIso_hom_snd, map_snd]
    ext n f
    rfl

/-- The full original relative corner retains its actual arrow-frame postcomposition arrow isomorphism. -/
def arrowPostcompIso {A B : CosimplicialObject C} (h : A ⟶ B)
    {X Y : C} (p : X ⟶ Y) :
    Arrow.mk (postcomp (arrowDiagram h) (identityToArrow p)) ≅ Arrow.mk (map h p) :=
  Arrow.isoMk (sourceArrowIso h X).symm (targetArrowIso h p) (by
    change (sourceArrowIso h X).inv ≫ map h p =
      postcomp (arrowDiagram h) (identityToArrow p) ≫ (targetArrowIso h p).hom
    rw [← arrow_postcomp_eq_map h p, ← Category.assoc, Iso.inv_hom_id, Category.id_comp])

/-- The full original source action keeps the composition of every original cosimplicial arrow. -/
theorem precomp_comp {A B D : CosimplicialObject C} (h : A ⟶ B) (k : B ⟶ D) (X : C) :
    precomp (h ≫ k) X = precomp k X ≫ precomp h X :=
  ResolutionHomComplex.precomp_comp h k _

/-- The full original coefficient action keeps the composition of every original base arrow. -/
theorem postcomp_comp (A : CosimplicialObject C) {X Y Z : C} (p : X ⟶ Y) (q : Y ⟶ Z) :
    postcomp A (p ≫ q) = postcomp A p ≫ postcomp A q := by
  ext n f
  change f ≫ (p ≫ q) = (f ≫ p) ≫ q
  exact (Category.assoc _ _ _).symm

/-- Every whole source and target action retains the original precomposition/postcomposition commutation. -/
theorem precomp_postcomp {A B : CosimplicialObject C} (h : A ⟶ B) {X Y : C} (p : X ⟶ Y) :
    precomp h X ≫ postcomp A p = postcomp B p ≫ precomp h Y :=
  ResolutionHomComplex.precomp_postcomp h _

/-- Every whole original source arrow square gives its actual contravariant target-pullback map. -/
def sourceTargetMap {A B A' B' : CosimplicialObject C} {h : A ⟶ B} {k : A' ⟶ B'}
    (s : Arrow.mk k ⟶ Arrow.mk h) {X Y : C} (p : X ⟶ Y) : target h p ⟶ target k p := by
  let a : A' ⟶ A := s.left
  let b : B' ⟶ B := s.right
  exact pullback.lift (pullback.fst (postcomp A p) (precomp h Y) ≫ precomp a X)
    (pullback.snd (postcomp A p) (precomp h Y) ≫ precomp b Y) (by
      have hw : a ≫ h = k ≫ b := s.w
      rw [Category.assoc, precomp_postcomp, ← Category.assoc, pullback.condition,
        Category.assoc, ← precomp_comp, hw, precomp_comp, ← Category.assoc])

/-- The whole original source-square action retains its original first target projection. -/
@[reassoc]
theorem sourceTargetMap_fst {A B A' B' : CosimplicialObject C} {h : A ⟶ B} {k : A' ⟶ B'}
    (s : Arrow.mk k ⟶ Arrow.mk h) {X Y : C} (p : X ⟶ Y) :
    sourceTargetMap s p ≫ pullback.fst (postcomp A' p) (precomp k Y) =
      pullback.fst (postcomp A p) (precomp h Y) ≫ precomp s.left X := pullback.lift_fst _ _ _

/-- The whole original source-square action retains its original second target projection. -/
@[reassoc]
theorem sourceTargetMap_snd {A B A' B' : CosimplicialObject C} {h : A ⟶ B} {k : A' ⟶ B'}
    (s : Arrow.mk k ⟶ Arrow.mk h) {X Y : C} (p : X ⟶ Y) :
    sourceTargetMap s p ≫ pullback.snd (postcomp A' p) (precomp k Y) =
      pullback.snd (postcomp A p) (precomp h Y) ≫ precomp s.right Y := pullback.lift_snd _ _ _

/-- The actual entire corner keeps naturality in every whole original cosimplicial-arrow square. -/
theorem map_naturality_source {A B A' B' : CosimplicialObject C} {h : A ⟶ B} {k : A' ⟶ B'}
    (s : Arrow.mk k ⟶ Arrow.mk h) {X Y : C} (p : X ⟶ Y) :
    precomp s.right X ≫ map k p = map h p ≫ sourceTargetMap s p := by
  apply pullback.hom_ext
  · rw [Category.assoc, map_fst, Category.assoc, sourceTargetMap_fst, ← Category.assoc, map_fst,
      ← precomp_comp, ← precomp_comp]
    exact congrArg (fun f => precomp f X) s.w.symm
  · rw [Category.assoc, map_snd, Category.assoc, sourceTargetMap_snd, ← Category.assoc, map_snd]
    exact precomp_postcomp s.right p

/-- Every whole original coefficient arrow square gives its actual covariant target-pullback map. -/
def coefficientTargetMap {A B : CosimplicialObject C} (h : A ⟶ B) {X Y X' Y' : C}
    {p : X ⟶ Y} {q : X' ⟶ Y'} (s : Arrow.mk p ⟶ Arrow.mk q) : target h p ⟶ target h q :=
  pullback.lift (pullback.fst (postcomp A p) (precomp h Y) ≫ postcomp A s.left)
    (pullback.snd (postcomp A p) (precomp h Y) ≫ postcomp B s.right) (by
      have hw : s.left ≫ q = p ≫ s.right := s.w
      rw [Category.assoc, ← postcomp_comp, hw, postcomp_comp, ← Category.assoc,
        pullback.condition, Category.assoc, precomp_postcomp, ← Category.assoc])

/-- The whole original coefficient-square action retains its original first target projection. -/
@[reassoc]
theorem coefficientTargetMap_fst {A B : CosimplicialObject C} (h : A ⟶ B) {X Y X' Y' : C}
    {p : X ⟶ Y} {q : X' ⟶ Y'} (s : Arrow.mk p ⟶ Arrow.mk q) :
    coefficientTargetMap h s ≫ pullback.fst (postcomp A q) (precomp h Y') =
      pullback.fst (postcomp A p) (precomp h Y) ≫ postcomp A s.left := pullback.lift_fst _ _ _

/-- The whole original coefficient-square action retains its original second target projection. -/
@[reassoc]
theorem coefficientTargetMap_snd {A B : CosimplicialObject C} (h : A ⟶ B) {X Y X' Y' : C}
    {p : X ⟶ Y} {q : X' ⟶ Y'} (s : Arrow.mk p ⟶ Arrow.mk q) :
    coefficientTargetMap h s ≫ pullback.snd (postcomp A q) (precomp h Y') =
      pullback.snd (postcomp A p) (precomp h Y) ≫ postcomp B s.right := pullback.lift_snd _ _ _

/-- The actual entire corner keeps naturality in every whole original coefficient-arrow square. -/
theorem map_naturality_target {A B : CosimplicialObject C} (h : A ⟶ B) {X Y X' Y' : C}
    {p : X ⟶ Y} {q : X' ⟶ Y'} (s : Arrow.mk p ⟶ Arrow.mk q) :
    map h p ≫ coefficientTargetMap h s = postcomp B s.left ≫ map h q := by
  apply pullback.hom_ext
  · rw [Category.assoc, coefficientTargetMap_fst, ← Category.assoc, map_fst,
      Category.assoc, map_fst]
    exact precomp_postcomp h s.left
  · rw [Category.assoc, coefficientTargetMap_snd, ← Category.assoc, map_snd,
      Category.assoc, map_snd, ← postcomp_comp, ← postcomp_comp]
    exact congrArg (postcomp B) s.w.symm

/-- The actual finite walking arrow has all direct arrows and only identity inverse arrows. -/
def walkingArrowReedy : CategoryTheory.ReedyStructure (Fin 2) (Fin 2) :=
  CategoryTheory.ReedyStructure.mk id ⊤ (fun {i j} _ => i = j) inferInstance
    { id_mem _ := rfl
      comp_mem _ _ hi hj := hi.trans hj }
    (fun f _ => leOfHom f)
    (fun _ h => le_of_eq h.symm)
    (fun _ _ h => ⟨h, Subsingleton.elim _ _⟩)
    (fun _ _ h => ⟨h, Subsingleton.elim _ _⟩)
    (fun {i j} f => ReedyFactorization.mk i (𝟙 i) f rfl trivial (Category.id_comp f))
    (fun {i j} f a b => by
      cases a with
      | mk am ai ad haF haI haD =>
        cases b with
        | mk bm bi bd hbF hbI hbD =>
          change i = am at haI
          change i = bm at hbI
          subst am
          subst bm
          have hi : ai = bi := Subsingleton.elim _ _
          have hd : ad = bd := Subsingleton.elim _ _
          cases hi
          cases hd
          rfl)

/-- The finite walking arrow has every original finite latching shape. -/
instance walkingArrowLatchingFinCategory (j : Fin 2) : FinCategory (walkingArrowReedy.Latching j) where
  fintypeObj := Fintype.ofFinite _
  fintypeHom := fun _ _ => Fintype.ofFinite _

/-- The finite walking arrow has every original finite matching shape. -/
instance walkingArrowMatchingFinCategory (j : Fin 2) : FinCategory (walkingArrowReedy.Matching j) where
  fintypeObj := Fintype.ofFinite _
  fintypeHom := fun _ _ => Fintype.ofFinite _

/-- The actual source arrow is its unchanged two-coefficient functor. -/
def toComposableArrows : Arrow C ⥤ ComposableArrows C 1 :=
  ComposableArrows.ofArrowFunctor

/-- The two-coefficient source functor returns its same whole original arrow. -/
def fromComposableArrows : ComposableArrows C 1 ⥤ Arrow C where
  obj f := Arrow.mk f.hom
  map f := Arrow.homMk (f.app 0) (f.app 1) (f.naturality (homOfLE (show (0 : Fin 2) ≤ 1 from by decide))).symm
  map_id f := by apply Arrow.hom_ext <;> rfl
  map_comp f g := by apply Arrow.hom_ext <;> rfl

/-- The actual arrow category and actual finite direct diagram category retain both original coefficients. -/
def walkingArrowEquivalence : Arrow C ≌ ComposableArrows C 1 where
  functor := ComposableArrows.ofArrowFunctor
  inverse := fromComposableArrows
  unitIso := NatIso.ofComponents (fun f => Iso.refl f) (by
    intro f g s
    apply Arrow.hom_ext
    · change s.left ≫ 𝟙 _ = 𝟙 _ ≫ s.left
      simp
    · change s.right ≫ 𝟙 _ = 𝟙 _ ≫ s.right
      simp)
  counitIso := NatIso.ofComponents
    (fun f => ComposableArrows.isoMk₁ (Iso.refl _) (Iso.refl _) (by
      change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
      simp))
    (by
      intro f g s
      apply ComposableArrows.hom_ext₁
      · change s.app 0 ≫ 𝟙 _ = 𝟙 _ ≫ s.app 0
        simp
      · change s.app 1 ≫ 𝟙 _ = 𝟙 _ ≫ s.app 1
        simp)
  functor_unitIso_comp f := by
    apply ComposableArrows.hom_ext₁
    · change (𝟙 f.left) ≫ 𝟙 _ = 𝟙 f.left
      exact Category.id_comp _
    · change (𝟙 f.right) ≫ 𝟙 _ = 𝟙 f.right
      exact Category.id_comp _

/-- Every matching shape of the actual finite direct arrow is empty. -/
instance walkingArrowMatchingEmpty (j : Fin 2) : IsEmpty (walkingArrowReedy.Matching j) :=
  ⟨fun a => by
    have he := a.obj.hom.property
    change j = walkingArrowReedy.matchingTarget a at he
    have hlt := a.property
    change walkingArrowReedy.matchingTarget a < j at hlt
    exact (lt_irrefl j) (by simpa only [← he] using hlt)⟩

/-- Every whole finite direct matching corner is the same component arrow through its actual terminal projection. -/
theorem walkingArrow_matchingCorner_iff [HasFiniteLimits C]
    (P : MorphismProperty C) [P.RespectsIso] {F G : ComposableArrows C 1} (s : F ⟶ G) (j : Fin 2) :
    P (CategoryTheory.ReedyStructure.matchingCorner walkingArrowReedy s j) ↔ P (s.app j) := by
  let _ : IsIso (limMap (walkingArrowReedy.matchingTransformation s j)) :=
    isIso_of_isTerminal
      (isLimitEquivIsTerminalOfIsEmpty C (limit.cone (walkingArrowReedy.matchingDiagram F j))
        (limit.isLimit _))
      (isLimitEquivIsTerminalOfIsEmpty C (limit.cone (walkingArrowReedy.matchingDiagram G j))
        (limit.isLimit _)) _
  let _ : IsIso (pullback.snd (limMap (walkingArrowReedy.matchingTransformation s j))
      (CategoryTheory.ReedyStructure.matchingMap walkingArrowReedy G j)) := inferInstance
  rw [← CategoryTheory.ReedyStructure.matchingCorner_snd walkingArrowReedy s j]
  exact (P.cancel_right_of_respectsIso _ _).symm

/-- The actual finite-arrow pushout corner keeps the original right map first and target arrow second. -/
def arrowCorner {f g : Arrow C} (s : f ⟶ g) [HasPushouts C] : pushout f.hom s.left ⟶ g.right :=
  pushout.desc s.right g.hom s.w.symm

/-- The whole finite-arrow corner retains its original right component. -/
@[reassoc]
theorem arrowCorner_inl {f g : Arrow C} (s : f ⟶ g) [HasPushouts C] :
    pushout.inl f.hom s.left ≫ arrowCorner s = s.right := pushout.inl_desc _ _ _

/-- The whole finite-arrow corner retains its original target arrow. -/
@[reassoc]
theorem arrowCorner_inr {f g : Arrow C} (s : f ⟶ g) [HasPushouts C] :
    pushout.inr f.hom s.left ≫ arrowCorner s = g.hom := pushout.inr_desc _ _ _

section ArrowModel

variable [ModelCategory C]
  (Fc : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (Ff : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

/-- The original two base factor factories construct the entire finite direct arrow model. -/
@[instance_reducible]
def arrowModel : ModelCategory (Arrow C) := by
  let _ : ModelCategory (ComposableArrows C 1) := ReedyModel.modelCategory walkingArrowReedy Fc Ff
  let _ : CategoryWithCofibrations (Arrow C) :=
    ⟨(cofibrations (ComposableArrows C 1)).inverseImage ComposableArrows.ofArrowFunctor⟩
  let _ : CategoryWithFibrations (Arrow C) :=
    ⟨(fibrations (ComposableArrows C 1)).inverseImage ComposableArrows.ofArrowFunctor⟩
  let _ : CategoryWithWeakEquivalences (Arrow C) :=
    ⟨(weakEquivalences (ComposableArrows C 1)).inverseImage ComposableArrows.ofArrowFunctor⟩
  exact ModelCategory.transport walkingArrowEquivalence rfl rfl rfl

/-- The constructed arrow model retains exactly both original coefficient weak equivalences. -/
theorem arrowModel_weak_iff {f g : Arrow C} (s : f ⟶ g) :
    letI := arrowModel Fc Ff
    weakEquivalences (Arrow C) s ↔ weakEquivalences C s.left ∧ weakEquivalences C s.right := by
  let _ := arrowModel Fc Ff
  change (∀ j : Fin 2, weakEquivalences C ((ComposableArrows.ofArrowFunctor.map s).app j)) ↔ _
  constructor
  · intro h
    exact ⟨h 0, h 1⟩
  · intro h j
    fin_cases j
    · exact h.1
    · exact h.2

/-- The constructed finite direct arrow model retains both original coefficient fibrations. -/
theorem arrowModel_fibration_iff {f g : Arrow C} (s : f ⟶ g) :
    letI := arrowModel Fc Ff
    fibrations (Arrow C) s ↔ fibrations C s.left ∧ fibrations C s.right := by
  let _ := arrowModel Fc Ff
  change (∀ j : Fin 2, fibrations C
    (CategoryTheory.ReedyStructure.matchingCorner walkingArrowReedy (ComposableArrows.ofArrowFunctor.map s) j)) ↔ _
  constructor
  · intro h
    exact ⟨(walkingArrow_matchingCorner_iff (fibrations C) _ 0).mp (h 0),
      (walkingArrow_matchingCorner_iff (fibrations C) _ 1).mp (h 1)⟩
  · intro h j
    apply (walkingArrow_matchingCorner_iff (fibrations C) _ j).mpr
    fin_cases j
    · exact h.1
    · exact h.2

/-- The constructed finite direct arrow model retains both original coefficient trivial fibrations. -/
theorem arrowModel_trivialFibration_iff {f g : Arrow C} (s : f ⟶ g) :
    letI := arrowModel Fc Ff
    trivialFibrations (Arrow C) s ↔ trivialFibrations C s.left ∧ trivialFibrations C s.right := by
  let _ := arrowModel Fc Ff
  change (fibrations (Arrow C) s ∧ weakEquivalences (Arrow C) s) ↔ _
  rw [arrowModel_fibration_iff Fc Ff, arrowModel_weak_iff Fc Ff]
  constructor
  · rintro ⟨⟨hl, hr⟩, ⟨wl, wr⟩⟩
    exact ⟨⟨hl, wl⟩, ⟨hr, wr⟩⟩
  · rintro ⟨⟨hl, wl⟩, ⟨hr, wr⟩⟩
    exact ⟨⟨hl, hr⟩, ⟨wl, wr⟩⟩

/-- The original left cofibration and original pushout-corner cofibration derive a cofibration in the
constructed arrow model. -/
theorem arrowModel_cof_of_left_corner {f g : Arrow C} (s : f ⟶ g)
    (hl : cofibrations C s.left) (hc : cofibrations C (arrowCorner s)) :
    letI := arrowModel Fc Ff
    cofibrations (Arrow C) s := by
  let _ := arrowModel Fc Ff
  rw [← trivialFibrations_llp (Arrow C)]
  intro U V p hp
  have hpt := (arrowModel_trivialFibration_iff Fc Ff p).mp hp
  let _ : Cofibration s.left := (cofibration_iff _).mpr hl
  let _ : Cofibration (arrowCorner s) := (cofibration_iff _).mpr hc
  let _ : Fibration p.left := (fibration_iff _).mpr hpt.1.1
  let _ : WeakEquivalence p.left := (weakEquivalence_iff _).mpr hpt.1.2
  let _ : Fibration p.right := (fibration_iff _).mpr hpt.2.1
  let _ : WeakEquivalence p.right := (weakEquivalence_iff _).mpr hpt.2.2
  refine ⟨fun {t b} sq => ?_⟩
  have hleft : t.left ≫ p.left = s.left ≫ b.left := congrArg Arrow.Hom.left sq.w
  let q₀ : CommSq t.left s.left p.left b.left := ⟨hleft⟩
  let l₀ : g.left ⟶ U.left := q₀.lift
  have h₀l : s.left ≫ l₀ = t.left := q₀.fac_left
  have h₀r : l₀ ≫ p.left = b.left := q₀.fac_right
  have ht : f.hom ≫ t.right = s.left ≫ (l₀ ≫ U.hom) := by
    rw [← Category.assoc, h₀l]
    exact t.w.symm
  let top : pushout f.hom s.left ⟶ U.right := pushout.desc t.right (l₀ ≫ U.hom) ht
  have hright : t.right ≫ p.right = s.right ≫ b.right := congrArg Arrow.Hom.right sq.w
  have hw : top ≫ p.right = arrowCorner s ≫ b.right := by
    apply pushout.hom_ext
    · rw [← Category.assoc, pushout.inl_desc, ← Category.assoc, arrowCorner_inl]
      exact hright
    · rw [← Category.assoc, pushout.inr_desc, Category.assoc, ← p.w, ← Category.assoc,
        h₀r, ← Category.assoc, arrowCorner_inr]
      exact b.w
  let q₁ : CommSq top (arrowCorner s) p.right b.right := ⟨hw⟩
  let l₁ : g.right ⟶ U.right := q₁.lift
  have h₁l : arrowCorner s ≫ l₁ = top := q₁.fac_left
  have h₁r : l₁ ≫ p.right = b.right := q₁.fac_right
  have hArrow : l₀ ≫ U.hom = g.hom ≫ l₁ := by
    have ht₁ := congrArg (fun k => pushout.inr f.hom s.left ≫ k) h₁l
    simpa only [top, ← Category.assoc, arrowCorner_inr, pushout.inr_desc] using ht₁.symm
  refine CommSq.HasLift.mk' { l := Arrow.homMk l₀ l₁ hArrow, fac_left := ?_, fac_right := ?_ }
  · apply Arrow.hom_ext
    · exact h₀l
    · have ht₁ := congrArg (fun k => pushout.inl f.hom s.left ≫ k) h₁l
      change s.right ≫ l₁ = t.right
      simpa only [top, ← Category.assoc, arrowCorner_inl, pushout.inl_desc] using ht₁
  · apply Arrow.hom_ext
    · exact h₀r
    · exact h₁r

/-- The same unchanged original coefficient p makes the actual identity-to-arrow map a constructed arrow-model
fibration. -/
theorem identityToArrow_fibration {X Y : C} (p : X ⟶ Y) [Fibration p] :
    letI := arrowModel Fc Ff
    Fibration (identityToArrow p) := by
  let _ := arrowModel Fc Ff
  apply (fibration_iff _).mpr
  apply (arrowModel_fibration_iff Fc Ff _).mpr
  exact ⟨(fibrations C).id_mem X, (fibration_iff p).mp inferInstance⟩

end ArrowModel

section ArrowLatching

variable [HasFiniteColimits C]

/-- Every original latching coefficient transformation keeps the whole original arrow colimit cocone. -/
def latchingArrowCocone {A B : CosimplicialObject C} (h : A ⟶ B) (n : SimplexCategory) :
    Cocone (SimplexCategory.reedy.latchingDiagram (arrowDiagram h) n) where
  pt := Arrow.mk (colimMap (SimplexCategory.reedy.latchingTransformation h n))
  ι.app a := Arrow.homMk (colimit.ι (SimplexCategory.reedy.latchingDiagram A n) a)
    (colimit.ι (SimplexCategory.reedy.latchingDiagram B n) a) (ι_colimMap _ a)
  ι.naturality {a b} f := by
    apply Arrow.hom_ext
    · exact (colimit.w (SimplexCategory.reedy.latchingDiagram A n) f).trans (Category.comp_id _).symm
    · exact (colimit.w (SimplexCategory.reedy.latchingDiagram B n) f).trans (Category.comp_id _).symm

/-- Every actual Arrow-valued cocone has its same whole original source coefficient cocone. -/
def latchingArrowSourceCocone {A B : CosimplicialObject C} (h : A ⟶ B) (n : SimplexCategory)
    (s : Cocone (SimplexCategory.reedy.latchingDiagram (arrowDiagram h) n)) :
    Cocone (SimplexCategory.reedy.latchingDiagram A n) where
  pt := s.pt.left
  ι.app a := (s.ι.app a).left
  ι.naturality {a b} f := by
    exact (congrArg Arrow.Hom.left (s.w f)).trans (Category.comp_id _).symm

/-- Every actual Arrow-valued cocone has its same whole original target coefficient cocone. -/
def latchingArrowTargetCocone {A B : CosimplicialObject C} (h : A ⟶ B) (n : SimplexCategory)
    (s : Cocone (SimplexCategory.reedy.latchingDiagram (arrowDiagram h) n)) :
    Cocone (SimplexCategory.reedy.latchingDiagram B n) where
  pt := s.pt.right
  ι.app a := (s.ι.app a).right
  ι.naturality {a b} f := by
    exact (congrArg Arrow.Hom.right (s.w f)).trans (Category.comp_id _).symm

/-- Every full original latching Arrow cocone has its actual universal original coefficient desc. -/
def latchingArrowDesc {A B : CosimplicialObject C} (h : A ⟶ B) (n : SimplexCategory)
    (s : Cocone (SimplexCategory.reedy.latchingDiagram (arrowDiagram h) n)) :
    (latchingArrowCocone h n).pt ⟶ s.pt :=
  Arrow.homMk (colimit.desc _ (latchingArrowSourceCocone h n s))
    (colimit.desc _ (latchingArrowTargetCocone h n s)) (by
      let l : colimit (SimplexCategory.reedy.latchingDiagram A n) ⟶ s.pt.left :=
        colimit.desc _ (latchingArrowSourceCocone h n s)
      let r : colimit (SimplexCategory.reedy.latchingDiagram B n) ⟶ s.pt.right :=
        colimit.desc _ (latchingArrowTargetCocone h n s)
      change l ≫ s.pt.hom = colimMap (SimplexCategory.reedy.latchingTransformation h n) ≫ r
      apply colimit.hom_ext
      intro a
      have hl : colimit.ι (SimplexCategory.reedy.latchingDiagram A n) a ≫ l = (s.ι.app a).left :=
        colimit.ι_desc _ a
      have hr : colimit.ι (SimplexCategory.reedy.latchingDiagram B n) a ≫ r = (s.ι.app a).right :=
        colimit.ι_desc _ a
      have hi := ι_colimMap (SimplexCategory.reedy.latchingTransformation h n) a
      exact ((Category.assoc _ _ _).symm.trans (congrArg (fun f => f ≫ s.pt.hom) hl)).trans
        ((s.ι.app a).w.trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun f => f ≫ r) hi).trans
              ((Category.assoc _ _ _).trans
                (congrArg (fun f => h.app (SimplexCategory.reedy.latchingSource a) ≫ f) hr)))).symm))

/-- The actual whole latching Arrow cocone is a colimit by both original coefficient universal properties. -/
def latchingArrowIsColimit {A B : CosimplicialObject C} (h : A ⟶ B) (n : SimplexCategory) :
    IsColimit (latchingArrowCocone h n) where
  desc := latchingArrowDesc h n
  fac s a := by
    apply Arrow.hom_ext
    · exact colimit.ι_desc _ a
    · exact colimit.ι_desc _ a
  uniq s m hm := by
    apply Arrow.hom_ext
    · apply colimit.hom_ext
      intro a
      exact (congrArg Arrow.Hom.left (hm a)).trans
        (colimit.ι_desc (latchingArrowSourceCocone h n s) a).symm
    · apply colimit.hom_ext
      intro a
      exact (congrArg Arrow.Hom.right (hm a)).trans
        (colimit.ι_desc (latchingArrowTargetCocone h n s) a).symm

/-- The actual canonical latching Arrow colimit is the same original latching coefficient arrow. -/
def latchingObjectArrowIso [HasFiniteColimits (Arrow C)] {A B : CosimplicialObject C}
    (h : A ⟶ B) (n : SimplexCategory) :
    colimit (SimplexCategory.reedy.latchingDiagram (arrowDiagram h) n) ≅
      Arrow.mk (colimMap (SimplexCategory.reedy.latchingTransformation h n)) :=
  colimit.isoColimitCocone ⟨latchingArrowCocone h n, latchingArrowIsColimit h n⟩

/-- Every original canonical latching injection keeps its whole source and target arrow coefficient. -/
@[reassoc]
theorem latchingObjectArrowIso_ι_hom [HasFiniteColimits (Arrow C)] {A B : CosimplicialObject C}
    (h : A ⟶ B) (n : SimplexCategory) (a : SimplexCategory.reedy.Latching n) :
    colimit.ι (SimplexCategory.reedy.latchingDiagram (arrowDiagram h) n) a ≫
      (latchingObjectArrowIso h n).hom = (latchingArrowCocone h n).ι.app a :=
  colimit.ι_desc _ a

/-- The original source and target latching maps retain the whole original coefficient-arrow square. -/
def arrowLatchingMap {A B : CosimplicialObject C} (h : A ⟶ B) (n : SimplexCategory) :
    Arrow.mk (colimMap (SimplexCategory.reedy.latchingTransformation h n)) ⟶ Arrow.mk (h.app n) :=
  Arrow.homMk (CategoryTheory.ReedyStructure.latchingMap SimplexCategory.reedy A n)
    (CategoryTheory.ReedyStructure.latchingMap SimplexCategory.reedy B n)
    (CategoryTheory.ReedyStructure.latchingMap_naturality SimplexCategory.reedy h n)

/-- The entire canonical latching Arrow map is the same original coefficient square through its actual colimit
isomorphism. -/
theorem latchingObjectArrowIso_hom_map [HasFiniteColimits (Arrow C)] {A B : CosimplicialObject C}
    (h : A ⟶ B) (n : SimplexCategory) :
    (latchingObjectArrowIso h n).hom ≫ arrowLatchingMap h n =
      CategoryTheory.ReedyStructure.latchingMap SimplexCategory.reedy (arrowDiagram h) n := by
  apply colimit.hom_ext
  intro a
  have ht : (latchingArrowCocone h n).ι.app a ≫ arrowLatchingMap h n =
      (arrowDiagram h).map (SimplexCategory.reedy.latchingArrow a) := by
    apply Arrow.hom_ext
    · exact CategoryTheory.ReedyStructure.latchingMap_ι SimplexCategory.reedy A n a
    · exact CategoryTheory.ReedyStructure.latchingMap_ι SimplexCategory.reedy B n a
  exact ((Category.assoc _ _ _).symm.trans
    (congrArg (fun f => f ≫ arrowLatchingMap h n) (latchingObjectArrowIso_ι_hom h n a))).trans
      (ht.trans (CategoryTheory.ReedyStructure.latchingMap_ι SimplexCategory.reedy (arrowDiagram h) n a).symm)

/-- The original full latching map in the arrow category retains both original coefficient latching maps. -/
def latchingMapArrowIso [HasFiniteColimits (Arrow C)] {A B : CosimplicialObject C}
    (h : A ⟶ B) (n : SimplexCategory) :
    Arrow.mk (CategoryTheory.ReedyStructure.latchingMap SimplexCategory.reedy (arrowDiagram h) n) ≅
      Arrow.mk (arrowLatchingMap h n) :=
  Arrow.isoMk (latchingObjectArrowIso h n) (Iso.refl (Arrow.mk (h.app n)))
    ((latchingObjectArrowIso_hom_map h n).trans (Category.comp_id _).symm)

/-- The original latching-arrow pushout corner is exactly the literal original relative latching corner after
the actual pushout symmetry. -/
theorem arrowLatchingMap_corner {A B : CosimplicialObject C} (h : A ⟶ B) (n : SimplexCategory) :
    arrowCorner (arrowLatchingMap h n) =
      (pushoutSymmetry (CategoryTheory.ReedyStructure.latchingMap SimplexCategory.reedy A n)
        (colimMap (SimplexCategory.reedy.latchingTransformation h n))).inv ≫
          CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedy h n := by
  change pushout.desc (CategoryTheory.ReedyStructure.latchingMap SimplexCategory.reedy B n) (h.app n)
    (CategoryTheory.ReedyStructure.latchingMap_naturality SimplexCategory.reedy h n).symm = _
  apply pushout.hom_ext
  · rw [pushout.inl_desc, ← Category.assoc, inl_comp_pushoutSymmetry_inv,
      CategoryTheory.ReedyStructure.latchingCorner_inr]
  · rw [pushout.inr_desc, ← Category.assoc, inr_comp_pushoutSymmetry_inv,
      CategoryTheory.ReedyStructure.latchingCorner_inl]

end ArrowLatching

section ArrowFrames

variable [ModelCategory C]
  (Fc : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (Ff : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

/-- The original A-frame latching cofibrations and h-relative latching cofibrations derive the full original
arrow frame's Reedy cofibrancy. -/
theorem arrowDiagram_latching_cofibration {A B : CosimplicialObject C} (h : A ⟶ B)
    (hA : ∀ n, cofibrations C (CategoryTheory.ReedyStructure.latchingMap SimplexCategory.reedy A n))
    (hh : ∀ n, cofibrations C (CategoryTheory.ReedyStructure.latchingCorner SimplexCategory.reedy h n)) :
    letI := arrowModel Fc Ff
    ∀ n, cofibrations (Arrow C)
      (CategoryTheory.ReedyStructure.latchingMap SimplexCategory.reedy (arrowDiagram h) n) := by
  let _ := arrowModel Fc Ff
  intro n
  have hc : cofibrations C (arrowCorner (arrowLatchingMap h n)) := by
    rw [arrowLatchingMap_corner]
    let e := pushoutSymmetry (CategoryTheory.ReedyStructure.latchingMap SimplexCategory.reedy A n)
      (colimMap (SimplexCategory.reedy.latchingTransformation h n))
    let _ : IsIso e.inv := e.isIso_inv
    exact (cofibrations C).comp_mem e.inv _ ((cofibrations C).of_isIso e.inv) (hh n)
  have hArrow : cofibrations (Arrow C) (arrowLatchingMap h n) :=
    arrowModel_cof_of_left_corner Fc Ff (arrowLatchingMap h n) (hA n) hc
  exact ((cofibrations (Arrow C)).arrow_mk_iso_iff (latchingMapArrowIso h n)).mpr hArrow

/-- The original weak-constant A and B frame operators derive every operator weak equivalence of the same entire
arrow frame. -/
theorem arrowDiagram_map_weak {A B : CosimplicialObject C} (h : A ⟶ B)
    (hA : ∀ {a b : SimplexCategory} (g : a ⟶ b), weakEquivalences C (A.map g))
    (hB : ∀ {a b : SimplexCategory} (g : a ⟶ b), weakEquivalences C (B.map g)) :
    letI := arrowModel Fc Ff
    ∀ {a b : SimplexCategory} (g : a ⟶ b), weakEquivalences (Arrow C) ((arrowDiagram h).map g) := by
  let _ := arrowModel Fc Ff
  intro a b g
  exact (arrowModel_weak_iff Fc Ff _).mpr ⟨hA g, hB g⟩

end ArrowFrames

end HomotopicalAlgebra.CosimplicialHomCorner
