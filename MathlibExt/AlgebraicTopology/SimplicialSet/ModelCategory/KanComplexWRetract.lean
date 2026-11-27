/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexW
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.RetractArrow

/-!
# Retract stability of `W` for Kan complexes

This module shows that the class `W` of weak equivalences between Kan complexes is
stable under retracts, via direct horn-filling for Kan structures and retract
arguments for the fundamental groupoid and homotopy groups.
-/

@[expose] public section

universe u

open CategoryTheory Simplicial

namespace SSet

namespace KanComplex

private lemma bijective_of_retract_functions {A B C D : Type u}
    {f : A → B} {g : C → D}
    (i₁ : A → C) (r₁ : C → A) (i₂ : B → D) (r₂ : D → B)
    (h_i : ∀ a, g (i₁ a) = i₂ (f a))
    (h_r : ∀ c, f (r₁ c) = r₂ (g c))
    (h_retract₁ : ∀ a, r₁ (i₁ a) = a)
    (h_retract₂ : ∀ b, r₂ (i₂ b) = b)
    (hg : Function.Bijective g) : Function.Bijective f := by
  constructor
  · intro a₁ a₂ hEq
    have h1 : g (i₁ a₁) = g (i₁ a₂) := by
      rw [h_i, h_i, hEq]
    have h2 : i₁ a₁ = i₁ a₂ := hg.1 h1
    have h3 : r₁ (i₁ a₁) = r₁ (i₁ a₂) := congrArg r₁ h2
    simpa [h_retract₁] using h3
  · intro b
    obtain ⟨c, hc⟩ := hg.2 (i₂ b)
    refine ⟨r₁ c, ?_⟩
    have h1 : f (r₁ c) = r₂ (g c) := h_r c
    rw [hc] at h1
    rw [h_retract₂] at h1
    exact h1

private lemma kanComplex_of_retract {X Z : SSet.{u}} (h : Retract X Z) [hz : KanComplex Z] :
    KanComplex X := by
  rw [KanComplex.iff] at hz ⊢
  intro n i f hf
  let fZ : ∀ (j : Fin (n + 2)) (_ : j ≠ i), Δ[n] ⟶ Z := fun j hj => f j hj ≫ h.i
  have hfZ : horn.IsCompatible fZ := by
    rcases n with _|n
    · trivial
    · intro j k hj hk hjk
      simp only [fZ]
      have hcomp := hf j k hj hk hjk
      simp only [← Category.assoc] at hcomp ⊢
      rw [hcomp]
  obtain ⟨φZ, hφZ⟩ := hz fZ hfZ
  refine ⟨φZ ≫ h.r, fun j hj => ?_⟩
  have h1 := hφZ j hj
  calc stdSimplex.δ j ≫ (φZ ≫ h.r) = (stdSimplex.δ j ≫ φZ) ≫ h.r := by simp
    _ = fZ j hj ≫ h.r := by rw [h1]
    _ = (f j hj ≫ h.i) ≫ h.r := rfl
    _ = f j hj ≫ (h.i ≫ h.r) := by simp [Category.assoc]
    _ = f j hj := by simp [h.retract]

private def fundamentalGroupoidFunctor : SSet.{u} ⥤ Cat.{u, u} where
  obj X := Cat.of (SSet.FundamentalGroupoid X)
  map f := (SSet.mapFundamentalGroupoid f).toCatHom
  map_id X := by
    apply Cat.Hom.ext
    dsimp
    have h1 : (truncation (2 : ℕ)).map (𝟙 X) =
        𝟙 ((truncation (2 : ℕ)).obj X) := by simp
    have h2 : SSet.mapFundamentalGroupoid (𝟙 X) =
        SSet.Truncated.mapFundamentalGroupoid
          (𝟙 ((truncation (2 : ℕ)).obj X)) := by
      unfold SSet.mapFundamentalGroupoid
      rw [h1]
    rw [h2]
    exact SSet.Truncated.mapFundamentalGroupoid_id
      ((truncation (2 : ℕ)).obj X)
  map_comp f g := by
    apply Cat.Hom.ext
    dsimp
    have h1 : (truncation (2 : ℕ)).map (f ≫ g) =
        (truncation (2 : ℕ)).map f ≫ (truncation (2 : ℕ)).map g := by simp
    have h2 : SSet.mapFundamentalGroupoid (f ≫ g) =
        SSet.Truncated.mapFundamentalGroupoid
          ((truncation (2 : ℕ)).map f ≫ (truncation (2 : ℕ)).map g) := by
      unfold SSet.mapFundamentalGroupoid
      rw [h1]
    rw [h2]
    exact SSet.Truncated.mapFundamentalGroupoid_comp
      ((truncation (2 : ℕ)).map f) ((truncation (2 : ℕ)).map g)

private lemma isEquivalence_of_retract_functor
    {X Y Z W₀ : SSet.{u}} {f : X ⟶ Y} {g : Z ⟶ W₀}
    (h : RetractArrow f g) [hgEquiv : (SSet.mapFundamentalGroupoid g).IsEquivalence] :
    (SSet.mapFundamentalGroupoid f).IsEquivalence := by
  let F : SSet.{u} ⥤ Cat.{u, u} := fundamentalGroupoidFunctor
  let e : SSet.FundamentalGroupoid Z ≌ SSet.FundamentalGroupoid W₀ :=
    Functor.asEquivalence (SSet.mapFundamentalGroupoid g)
  let eCat : Bicategory.Equivalence (F.obj Z) (F.obj W₀) :=
    Bicategory.Equivalence.mkOfAdjointifyCounit (f := F.map g) (g := e.inverse.toCatHom)
      (Cat.Hom.isoMk e.unitIso) (Cat.Hom.isoMk e.counitIso)
  let Fps := F.toPseudofunctor'
  have hRetractLoc : Bicategory.RetractArrow₁ (Quiver.Hom.toLoc f) (Quiver.Hom.toLoc g) :=
    h.toLoc
  have hRetractCat : Bicategory.RetractArrow₁ (Fps.map (Quiver.Hom.toLoc f))
      (Fps.map (Quiver.Hom.toLoc g)) :=
    hRetractLoc.map Fps
  have hRetractCat' : Bicategory.RetractArrow₁ (F.map f) (F.map g) :=
    hRetractCat
  let e' : Bicategory.Equivalence (F.obj X) (F.obj Y) :=
    Bicategory.RetractArrow₁.equivalence (f := eCat) hRetractCat'
  have hIsEquiv : (SSet.mapFundamentalGroupoid f).IsEquivalence := by
    have hHom : e'.hom.toFunctor = SSet.mapFundamentalGroupoid f := rfl
    have hUnit' : 𝟭 ↑(F.obj X) ≅ e'.hom.toFunctor ⋙ e'.inv.toFunctor :=
      Cat.Hom.toNatIso e'.unit
    have hCounit' : e'.inv.toFunctor ⋙ e'.hom.toFunctor ≅ 𝟭 ↑(F.obj Y) :=
      Cat.Hom.toNatIso e'.counit
    have hUnit2 :
        𝟭 (SSet.FundamentalGroupoid X) ≅
          SSet.mapFundamentalGroupoid f ⋙ e'.inv.toFunctor := by
      change 𝟭 ↑(F.obj X) ≅ SSet.mapFundamentalGroupoid f ⋙ e'.inv.toFunctor
      rw [← hHom]
      exact hUnit'
    have hCounit2 :
        e'.inv.toFunctor ⋙ SSet.mapFundamentalGroupoid f ≅
          𝟭 (SSet.FundamentalGroupoid Y) := by
      change e'.inv.toFunctor ⋙ SSet.mapFundamentalGroupoid f ≅ 𝟭 ↑(F.obj Y)
      rw [← hHom]
      exact hCounit'
    exact Functor.IsEquivalence.mk' e'.inv.toFunctor hUnit2 hCounit2
  exact hIsEquiv

private lemma bijective_piMap_of_retract {X Y Z W₀ : SSet.{u}}
    {f : X ⟶ Y} {g : Z ⟶ W₀} (h : RetractArrow f g)
    (hg : ∀ (n : ℕ) (z : Z _⦋0⦌), Function.Bijective (KanComplex.π.map g rfl (n := n) (x := z)))
    (n : ℕ) (x : X _⦋0⦌) :
    Function.Bijective (KanComplex.π.map f rfl (n := n) (x := x)) := by
  let zx : Z _⦋0⦌ := h.i.left.app _ x
  let y : Y _⦋0⦌ := f.app _ x
  let wy : W₀ _⦋0⦌ := g.app _ zx
  have h_y_eq : h.i.right.app _ y = wy := by
    calc h.i.right.app _ y = h.i.right.app _ (f.app _ x) := rfl
      _ = (f ≫ h.i.right).app _ x := rfl
      _ = (h.i.left ≫ g).app _ x := congrArg (fun k => k.app _ x) h.i.w.symm
      _ = g.app _ (h.i.left.app _ x) := rfl
      _ = wy := rfl
  have h_r_left_eq : h.r.left.app _ zx = x := by
    calc h.r.left.app _ zx = h.r.left.app _ (h.i.left.app _ x) := rfl
      _ = (h.i.left ≫ h.r.left).app _ x := rfl
      _ = (𝟙 X : X ⟶ X).app _ x := congrArg (fun k => k.app _ x) h.retract_left
      _ = x := rfl
  have h_r_right_eq : h.r.right.app _ wy = y := by
    calc h.r.right.app _ wy = h.r.right.app _ (g.app _ zx) := rfl
      _ = (g ≫ h.r.right).app _ zx := rfl
      _ = (h.r.left ≫ f).app _ zx := congrArg (fun k => k.app _ zx) h.r.w.symm
      _ = f.app _ (h.r.left.app _ zx) := rfl
      _ = f.app _ x := congrArg (fun a => f.app _ a) h_r_left_eq
      _ = y := rfl
  have h_i_left_g_eq : (h.i.left ≫ g).app _ x = wy := rfl
  have h_f_i_right_eq : (f ≫ h.i.right).app _ x = wy := by
    calc (f ≫ h.i.right).app _ x = h.i.right.app _ (f.app _ x) := rfl
      _ = h.i.right.app _ y := rfl
      _ = wy := h_y_eq
  have h_r_left_f_eq : (h.r.left ≫ f).app _ zx = y := by
    calc (h.r.left ≫ f).app _ zx = f.app _ (h.r.left.app _ zx) := rfl
      _ = f.app _ x := by rw [h_r_left_eq]
      _ = y := rfl
  have h_g_r_right_eq : (g ≫ h.r.right).app _ zx = y := by
    calc (g ≫ h.r.right).app _ zx = h.r.right.app _ (g.app _ zx) := rfl
      _ = h.r.right.app _ wy := rfl
      _ = y := h_r_right_eq
  have h_i_r_left_eq : (h.i.left ≫ h.r.left).app _ x = x := by
    calc (h.i.left ≫ h.r.left).app _ x = h.r.left.app _ (h.i.left.app _ x) := rfl
      _ = h.r.left.app _ zx := rfl
      _ = x := h_r_left_eq
  have h_i_r_right_eq : (h.i.right ≫ h.r.right).app _ y = y := by
    calc (h.i.right ≫ h.r.right).app _ y = h.r.right.app _ (h.i.right.app _ y) := rfl
      _ = h.r.right.app _ wy := by rw [h_y_eq]
      _ = y := h_r_right_eq
  let i₁ : KanComplex.π n X x → KanComplex.π n Z zx :=
    KanComplex.π.map h.i.left rfl n
  let r₁ : KanComplex.π n Z zx → KanComplex.π n X x :=
    KanComplex.π.map h.r.left h_r_left_eq n
  let i₂ : KanComplex.π n Y y → KanComplex.π n W₀ wy :=
    KanComplex.π.map h.i.right h_y_eq n
  let r₂ : KanComplex.π n W₀ wy → KanComplex.π n Y y :=
    KanComplex.π.map h.r.right h_r_right_eq n
  have hgBij := hg n zx
  apply bijective_of_retract_functions i₁ r₁ i₂ r₂ _ _ _ _ hgBij
  · intro a
    have h1 : KanComplex.π.map g rfl n (KanComplex.π.map h.i.left rfl n a) =
        KanComplex.π.map (h.i.left ≫ g) h_i_left_g_eq n a := by
      rw [← KanComplex.π.map_comp_apply (f := h.i.left) (g := g)
        (hx := rfl) (hy := rfl) (h := h_i_left_g_eq)]
    have h2 : KanComplex.π.map (f ≫ h.i.right) h_f_i_right_eq n a =
        KanComplex.π.map h.i.right h_y_eq n (KanComplex.π.map f rfl n a) := by
      rw [KanComplex.π.map_comp_apply (f := f) (g := h.i.right)
        (hx := rfl) (hy := h_y_eq) (h := h_f_i_right_eq)]
    have h_mid : KanComplex.π.map (h.i.left ≫ g) h_i_left_g_eq n a =
        KanComplex.π.map (f ≫ h.i.right) h_f_i_right_eq n a := by
      have hEq := π.map_congr h.i.w h_i_left_g_eq h_f_i_right_eq n
      exact congrFun hEq a
    calc KanComplex.π.map g rfl n (KanComplex.π.map h.i.left rfl n a)
        = KanComplex.π.map (h.i.left ≫ g) h_i_left_g_eq n a := h1
      _ = KanComplex.π.map (f ≫ h.i.right) h_f_i_right_eq n a := h_mid
      _ = KanComplex.π.map h.i.right h_y_eq n (KanComplex.π.map f rfl n a) := h2
  · intro c
    have h1 : KanComplex.π.map f rfl n (KanComplex.π.map h.r.left h_r_left_eq n c) =
        KanComplex.π.map (h.r.left ≫ f) h_r_left_f_eq n c := by
      rw [← KanComplex.π.map_comp_apply (f := h.r.left) (g := f)
        (hx := h_r_left_eq) (hy := rfl) (h := h_r_left_f_eq)]
    have h2 : KanComplex.π.map (g ≫ h.r.right) h_g_r_right_eq n c =
        KanComplex.π.map h.r.right h_r_right_eq n (KanComplex.π.map g rfl n c) := by
      rw [KanComplex.π.map_comp_apply (f := g) (g := h.r.right)
        (hx := rfl) (hy := h_r_right_eq) (h := h_g_r_right_eq)]
    have h_mid : KanComplex.π.map (h.r.left ≫ f) h_r_left_f_eq n c =
        KanComplex.π.map (g ≫ h.r.right) h_g_r_right_eq n c := by
      have hEq := π.map_congr h.r.w h_r_left_f_eq h_g_r_right_eq n
      exact congrFun hEq c
    calc KanComplex.π.map f rfl n (KanComplex.π.map h.r.left h_r_left_eq n c)
        = KanComplex.π.map (h.r.left ≫ f) h_r_left_f_eq n c := h1
      _ = KanComplex.π.map (g ≫ h.r.right) h_g_r_right_eq n c := h_mid
      _ = KanComplex.π.map h.r.right h_r_right_eq n (KanComplex.π.map g rfl n c) := h2
  · intro a
    have h1 : KanComplex.π.map h.r.left h_r_left_eq n (KanComplex.π.map h.i.left rfl n a) =
        KanComplex.π.map (h.i.left ≫ h.r.left) h_i_r_left_eq n a := by
      rw [← KanComplex.π.map_comp_apply (f := h.i.left) (g := h.r.left)
        (hx := rfl) (hy := h_r_left_eq) (h := h_i_r_left_eq)]
    have h2 : KanComplex.π.map (h.i.left ≫ h.r.left) h_i_r_left_eq n a =
        KanComplex.π.map (𝟙 X : X ⟶ X) rfl n a := by
      have hEq := π.map_congr h.retract_left h_i_r_left_eq rfl n
      exact congrFun hEq a
    have h3 : KanComplex.π.map (𝟙 X : X ⟶ X) rfl n a = a :=
      KanComplex.π.map_id_apply (X := X) (n := n) (x := x) a
    exact (h1.trans h2).trans h3
  · intro b
    have h1 : KanComplex.π.map h.r.right h_r_right_eq n (KanComplex.π.map h.i.right h_y_eq n b) =
        KanComplex.π.map (h.i.right ≫ h.r.right) h_i_r_right_eq n b := by
      rw [← KanComplex.π.map_comp_apply (f := h.i.right) (g := h.r.right)
        (hx := h_y_eq) (hy := h_r_right_eq) (h := h_i_r_right_eq)]
    have h2 : KanComplex.π.map (h.i.right ≫ h.r.right) h_i_r_right_eq n b =
        KanComplex.π.map (𝟙 Y : Y ⟶ Y) rfl n b := by
      have hEq := π.map_congr h.retract_right h_i_r_right_eq rfl n
      exact congrFun hEq b
    have h3 : KanComplex.π.map (𝟙 Y : Y ⟶ Y) rfl n b = b :=
      KanComplex.π.map_id_apply (X := Y) (n := n) (x := y) b
    exact (h1.trans h2).trans h3

/-- `W` is stable under retracts: a retract of a weak equivalence is a weak
equivalence. -/
theorem W.of_retract {X Y Z W₀ : SSet.{u}} {f : X ⟶ Y} {g : Z ⟶ W₀}
    (h : RetractArrow f g) (hg : W g) : W f := by
  obtain ⟨hz, hw, hgEquiv, hgBij⟩ := hg
  have hx : KanComplex X := kanComplex_of_retract h.left
  have hy : KanComplex Y := kanComplex_of_retract h.right
  refine W.mk f hx hy ?_ ?_
  · exact isEquivalence_of_retract_functor h
  · intro n x
    exact bijective_piMap_of_retract h hgBij n x

/-- `W` is stable under retracts. -/
instance W.isStableUnderRetracts : W.IsStableUnderRetracts where
  of_retract := W.of_retract

end KanComplex

end SSet
