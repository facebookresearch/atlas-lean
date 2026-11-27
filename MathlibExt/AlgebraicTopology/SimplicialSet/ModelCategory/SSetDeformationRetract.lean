/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.PathSpace
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

@[expose] public section

open CategoryTheory Simplicial SSet Limits MonoidalCategory CartesianMonoidalCategory
open SSet.modelCategoryQuillen

universe u

namespace SSet

-- Binder `hx` in `stationary` is part of the public field signature; keep the name.
set_option linter.unusedVariables false in
/-- A homotopy relative to a subcomplex `S ≤ X`, stationary on `S`.

For `f g : X ⟶ Y`, a witness `H : HomotopyRel f g S` consists of
`h : X ⊗ Δ[1] ⟶ Y` with `ι₀ ≫ h = f`, `ι₁ ≫ h = g`,
and `h` constant on `S` in the interval direction:
`∀ x ∈ S, ∀ t : Δ[1], h (x, t) = f x`.

This reuses `SSet.Homotopy` (`RelativeMorphism.Homotopy` with `⊥`)
but adds the relative stationarity condition, modelling
`TopCat`'s `ContinuousMap.HomotopyRel` with interval `Δ[1]`. -/
structure HomotopyRel {X Y : SSet.{u}} (f g : X ⟶ Y) (S : X.Subcomplex) where
  h : X ⊗ (Δ[1] : SSet.{u}) ⟶ Y
  h₀ : SSet.ι₀ ≫ h = f
  h₁ : SSet.ι₁ ≫ h = g
  stationary : ∀ {n : SimplexCategoryᵒᵖ} (x : X.obj n) (hx : x ∈ S.obj n)
      (t : (Δ[1] : SSet.{u}).obj n), h.app n ⟨x, t⟩ = f.app n x

namespace HomotopyRel

variable {X Y : SSet.{u}} {f g : X ⟶ Y} {S : X.Subcomplex}

@[reassoc (attr := simp)]
lemma h₀_assoc (H : HomotopyRel f g S) : SSet.ι₀ ≫ H.h = f := H.h₀

@[reassoc (attr := simp)]
lemma h₁_assoc (H : HomotopyRel f g S) : SSet.ι₁ ≫ H.h = g := H.h₁

/-- Constant homotopy relative to any subcomplex. -/
noncomputable def refl (f : X ⟶ Y) (S : X.Subcomplex) : HomotopyRel f f S where
  h := fst _ _ ≫ f
  h₀ := by simp
  h₁ := by simp
  stationary := by
    intro n x _ t
    rfl

end HomotopyRel

/-- Forget the stationarity condition: a homotopy relative to `S` yields an ordinary homotopy. -/
def HomotopyRel.toHomotopy {X Y : SSet.{u}} {f g : X ⟶ Y} {S : X.Subcomplex}
    (H : HomotopyRel f g S) : SSet.Homotopy f g where
  h := H.h
  h₀ := H.h₀
  h₁ := H.h₁
  rel := by ext n ⟨⟨x, hx⟩, t⟩; cases hx

/-- Categorical form of `HomotopyRel.stationary`: the homotopy is constant on `S`
in the interval direction.

For `H : HomotopyRel f g S`, whiskering the inclusion `S.ι` with `Δ[1]`
followed by `H.h` equals the first projection followed by the inclusion and `f`:

`(S.ι ▷ Δ[1]) ≫ H.h = fst S Δ[1] ≫ S.ι ≫ f`.

This is the natural-transformation equality underlying the pointwise
stationarity condition, formulated for rewriting with `Functor.map_comp`. -/
@[reassoc]
theorem HomotopyRel.stationary_eq {X Y : SSet.{u}} {f g : X ⟶ Y} {S : X.Subcomplex}
    (H : HomotopyRel f g S) :
    (S.ι ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst (S : SSet.{u}) (Δ[1] : SSet.{u}) ≫ S.ι ≫ f := by
  ext n ⟨⟨x, hx⟩, t⟩
  exact H.stationary x hx t

/-- A strong deformation retract in `SSet`.

For `f : X ⟶ Y`, a witness consists of a retraction `r : Y ⟶ X`
with `f ≫ r = 𝟙 X` and a homotopy `H : HomotopyRel (𝟙 Y) (r ≫ f) (range f)`
stationary on the simplicial image `range f ≤ Y`.

Orientation follows `TopCat` `StrongDeformationRetract`:
`H 0 = 𝟙 Y`, `H 1 = r ≫ f`, stationary on `Set.range f`. -/
structure StrongDeformationRetract {X Y : SSet.{u}} (f : X ⟶ Y) where
  r : Y ⟶ X
  retract : f ≫ r = 𝟙 X
  homotopy : HomotopyRel (𝟙 Y) (r ≫ f) (Subcomplex.range f)

/-- The `MorphismProperty` of being a strong deformation retract. -/
def strongDeformationRetract : MorphismProperty SSet.{u} :=
  fun _ _ f => Nonempty (StrongDeformationRetract f)

theorem mem_strongDeformationRetract_iff {X Y : SSet.{u}} {f : X ⟶ Y} :
    strongDeformationRetract f ↔ Nonempty (StrongDeformationRetract f) :=
  Iff.rfl

theorem strongDeformationRetract_iff {X Y : SSet.{u}} {f : X ⟶ Y} :
    strongDeformationRetract f ↔
      ∃ (r : Y ⟶ X) (_ : f ≫ r = 𝟙 X)
        (_ : HomotopyRel (𝟙 Y) (r ≫ f) (Subcomplex.range f)), True := by
  constructor
  · rintro ⟨w⟩
    exact ⟨w.r, w.retract, w.homotopy, True.intro⟩
  · rintro ⟨r, hr, H, _⟩
    exact ⟨⟨r, hr, H⟩⟩

instance : (strongDeformationRetract : MorphismProperty SSet.{u}).RespectsIso := by
  refine MorphismProperty.RespectsIso.mk _ ?_ ?_
  · intro X Y Z e f hf
    obtain ⟨w⟩ := hf
    -- New retraction `Z → X` is `w.r ≫ e.inv`
    refine ⟨⟨w.r ≫ e.inv, ?_, ?_⟩⟩
    · calc (e.hom ≫ f) ≫ (w.r ≫ e.inv)
          = e.hom ≫ (f ≫ w.r) ≫ e.inv := by simp only [Category.assoc]
        _ = e.hom ≫ 𝟙 Y ≫ e.inv := by rw [w.retract]
        _ = e.hom ≫ e.inv := by simp
        _ = 𝟙 X := Iso.hom_inv_id e
    · -- Homotopy target equality
      have h_target : w.r ≫ f = (w.r ≫ e.inv) ≫ (e.hom ≫ f) := by
        calc w.r ≫ f = w.r ≫ 𝟙 Y ≫ f := by simp
          _ = w.r ≫ (e.inv ≫ e.hom) ≫ f := by rw [Iso.inv_hom_id]
          _ = (w.r ≫ e.inv) ≫ (e.hom ≫ f) := by simp only [Category.assoc]
      -- Range equality: `range (e.hom ≫ f) = range f` since `e.hom` is iso (levelwise bijective)
      have h_range : Subcomplex.range (e.hom ≫ f) = Subcomplex.range f := by
        ext n y
        simp only [Subcomplex.range, Subfunctor.range_obj, Set.mem_range]
        constructor
        · rintro ⟨a, ha⟩
          -- `(e.hom ≫ f).app n a = f.app n (e.hom.app n a) = y`
          exact ⟨e.hom.app n a, ha⟩
        · rintro ⟨b, hb⟩
          -- `e.hom` is iso, so `b = e.hom (e.inv b)`
          refine ⟨e.inv.app n b, ?_⟩
          have h_inv_hom : (e.inv ≫ e.hom : Y ⟶ Y).app n b = b := by
            have h_id : e.inv ≫ e.hom = 𝟙 Y := Iso.inv_hom_id e
            rw [h_id]; rfl
          have h_eq : e.hom.app n (e.inv.app n b) = b := by
            simp
          have hb' : f.app n b = y := hb
          rw [← h_eq] at hb'
          exact hb'
      -- Transport homotopy via equalities
      have H0 := w.homotopy
      -- Rewrite homotopy to have correct target and subcomplex
      let H1 : HomotopyRel (𝟙 Z) ((w.r ≫ e.inv) ≫ (e.hom ≫ f))
          (Subcomplex.range (e.hom ≫ f)) :=
        ⟨H0.h, H0.h₀, by rw [← h_target]; exact H0.h₁, by
          intro n x hx t
          have hx' : x ∈ (Subcomplex.range f).obj n := by
            rw [h_range] at hx
            exact hx
          -- `H0.stationary` gives `H0.h.app n ⟨x,t⟩ = (𝟙 Z).app n x = x`
          have hstat := H0.stationary (x := x) hx' t
          -- `f₀ = 𝟙 Z`, so `f₀.app n x = x`
          simpa using hstat⟩
      exact H1
  · intro X Y Z e f hf
    obtain ⟨w⟩ := hf
    -- New maps: `f' = f ≫ e.hom : X ⟶ Z`, `r' = e.inv ≫ w.r : Z ⟶ X`
    let r' : Z ⟶ X := e.inv ≫ w.r
    let f' : X ⟶ Z := f ≫ e.hom
    have h_rf : r' ≫ f' = e.inv ≫ (w.r ≫ f) ≫ e.hom := by
      simp only [r', f', Category.assoc]
    refine ⟨⟨r', ?_, ?_⟩⟩
    · calc f' ≫ r' = (f ≫ e.hom) ≫ (e.inv ≫ w.r) := rfl
        _ = f ≫ (e.hom ≫ e.inv) ≫ w.r := by simp only [Category.assoc]
        _ = f ≫ 𝟙 Y ≫ w.r := by rw [Iso.hom_inv_id]
        _ = f ≫ w.r := by simp
        _ = 𝟙 X := w.retract
    · -- Construct `H' : Z ⊗ Δ[1] ⟶ Z` as `(e.inv ▷ Δ[1]) ≫ w.homotopy.h ≫ e.hom`
      let H0 := w.homotopy
      let h' : Z ⊗ (Δ[1] : SSet.{u}) ⟶ Z :=
        (e.inv ▷ (Δ[1] : SSet.{u})) ≫ H0.h ≫ e.hom
      have h₀' : SSet.ι₀ ≫ h' = 𝟙 Z := by
        calc SSet.ι₀ ≫ h'
            = SSet.ι₀ ≫ (e.inv ▷ (Δ[1] : SSet.{u})) ≫ H0.h ≫ e.hom := by
              simp only [h']
          _ = (e.inv ≫ SSet.ι₀) ≫ H0.h ≫ e.hom := by
              rw [SSet.ι₀_comp_assoc]
              simp only [Category.assoc]
          _ = e.inv ≫ (SSet.ι₀ ≫ H0.h) ≫ e.hom := by simp only [Category.assoc]
          _ = e.inv ≫ 𝟙 Y ≫ e.hom := by rw [H0.h₀]
          _ = e.inv ≫ e.hom := by simp
          _ = 𝟙 Z := Iso.inv_hom_id e
      have h₁' : SSet.ι₁ ≫ h' = r' ≫ f' := by
        calc SSet.ι₁ ≫ h'
            = SSet.ι₁ ≫ (e.inv ▷ (Δ[1] : SSet.{u})) ≫ H0.h ≫ e.hom := by
              simp only [h']
          _ = (e.inv ≫ SSet.ι₁) ≫ H0.h ≫ e.hom := by
              rw [SSet.ι₁_comp_assoc]
              simp only [Category.assoc]
          _ = e.inv ≫ (SSet.ι₁ ≫ H0.h) ≫ e.hom := by simp only [Category.assoc]
          _ = e.inv ≫ (w.r ≫ f) ≫ e.hom := by rw [H0.h₁]
          _ = r' ≫ f' := by simp only [r', f', h_rf, Category.assoc]
      refine ⟨h', h₀', h₁', ?_⟩
      -- Stationary on `range f'` : for `x ∈ range (f ≫ e.hom)`, `h' (x,t) = x`
      intro n x hx t
      -- Unfold `h'` at the simplex level: `h'.app n ⟨x,t⟩ = e.hom.app n (H0.h.app n ⟨e.inv.app n x,
      -- t⟩)`
      have h_app : h'.app n ⟨x, t⟩ = e.hom.app n (H0.h.app n ⟨e.inv.app n x, t⟩) := by
        -- ` (e.inv ▷ Δ[1]).app n ⟨x,t⟩ = ⟨e.inv.app n x, t⟩`
        have h1 : (e.inv ▷ (Δ[1] : SSet.{u})).app n ⟨x, t⟩ = ⟨e.inv.app n x, t⟩ := rfl
        change e.hom.app n (H0.h.app n ((e.inv ▷ (Δ[1] : SSet.{u})).app n ⟨x, t⟩)) = _
        rw [h1]
      rw [h_app]
      -- Show `e.inv.app n x ∈ range f`
      have hx_inv : e.inv.app n x ∈ (Subcomplex.range f).obj n := by
        -- `x ∈ range (f ≫ e.hom)` means `∃ a, (f ≫ e.hom).app n a = x`
        have hx_range : x ∈ (Subcomplex.range f').obj n := hx
        simp only [f', Subcomplex.range, Subfunctor.range_obj, Set.mem_range] at hx_range
        obtain ⟨a, ha⟩ := hx_range
        have ha' : (f ≫ e.hom).app n a = x := ha
        have h_eq : e.inv.app n x = f.app n a := by
          calc e.inv.app n x = e.inv.app n ((f ≫ e.hom).app n a) := by rw [ha']
            _ = e.inv.app n (e.hom.app n (f.app n a)) := rfl
            _ = f.app n a := by
                -- `e.hom ≫ e.inv = 𝟙 Y` pointwise, so `e.inv (e.hom (f a)) = f a`
                have h_comp : (e.hom ≫ e.inv : Y ⟶ Y).app n (f.app n a) = f.app n a := by
                  have h_id : e.hom ≫ e.inv = 𝟙 Y := Iso.hom_inv_id e
                  rw [h_id]; rfl
                simp
        rw [h_eq]
        exact ⟨a, rfl⟩
      -- Apply stationarity of `H0` on `range f`
      have hstat := H0.stationary (x := e.inv.app n x) hx_inv t
      -- `H0` is relative to `𝟙 Y`, so `H0.h.app n ⟨e.inv x, t⟩ = e.inv x`
      have h_eq2 : H0.h.app n ⟨e.inv.app n x, t⟩ = e.inv.app n x := by
        simpa using hstat
      rw [h_eq2]
      -- `e.hom (e.inv x) = x`
      have h_inv_hom : e.hom.app n (e.inv.app n x) = x := by
        have h_comp : (e.inv ≫ e.hom : Z ⟶ Z).app n x = x := by
          have h_id' : e.inv ≫ e.hom = 𝟙 Z := Iso.inv_hom_id e
          rw [h_id']; rfl
        simp
      exact h_inv_hom

instance : (strongDeformationRetract : MorphismProperty SSet.{u}).IsStableUnderCobaseChange where
  of_isPushout {A A' B B' f g f' g'} sq hf := by
    obtain ⟨w⟩ := hf
    have h_comm : g ≫ 𝟙 B = f ≫ (w.r ≫ g) := by
      calc g ≫ 𝟙 B = g := by simp
        _ = 𝟙 A ≫ g := by simp
        _ = (f ≫ w.r) ≫ g := by rw [w.retract]
        _ = f ≫ (w.r ≫ g) := by simp [Category.assoc]
    let r' : B' ⟶ B := sq.desc (𝟙 B) (w.r ≫ g) h_comm
    have hr' : f' ≫ r' = 𝟙 B := sq.inl_desc (𝟙 B) (w.r ≫ g) h_comm
    have hg' : g' ≫ r' = w.r ≫ g := sq.inr_desc (𝟙 B) (w.r ≫ g) h_comm
    let h_B : B ⊗ (Δ[1] : SSet.{u}) ⟶ B' := fst B (Δ[1] : SSet.{u}) ≫ f'
    let h_A' : A' ⊗ (Δ[1] : SSet.{u}) ⟶ B' := w.homotopy.h ≫ g'
    have h_f_eq : (f ▷ (Δ[1] : SSet.{u})) ≫ w.homotopy.h = fst A (Δ[1] : SSet.{u}) ≫ f := by
      ext n ⟨a, t⟩
      have hx : f.app n a ∈ (Subcomplex.range f).obj n := ⟨a, rfl⟩
      have hstat := w.homotopy.stationary (f.app n a) hx t
      change (w.homotopy.h.app n ((f ▷ (Δ[1] : SSet.{u})).app n ⟨a, t⟩)) =
        (f.app n ((fst A (Δ[1] : SSet.{u})).app n ⟨a, t⟩))
      simp only at hstat ⊢
      exact hstat
    have h_glue : (g ▷ (Δ[1] : SSet.{u})) ≫ h_B =
        (f ▷ (Δ[1] : SSet.{u})) ≫ h_A' := by
      ext n ⟨a, t⟩
      have hx : f.app n a ∈ (Subcomplex.range f).obj n := ⟨a, rfl⟩
      have hstat := w.homotopy.stationary (f.app n a) hx t
      have hw : f'.app n (g.app n a) = g'.app n (f.app n a) := by
        change (g ≫ f').app n a = (f ≫ g').app n a
        exact congr_fun (congr_arg (fun h => h.app n) sq.w) a
      change h_B.app n ((g ▷ (Δ[1] : SSet.{u})).app n ⟨a, t⟩) =
        h_A'.app n ((f ▷ (Δ[1] : SSet.{u})).app n ⟨a, t⟩)
      change f'.app n (g.app n a) = g'.app n (w.homotopy.h.app n ⟨f.app n a, t⟩)
      rw [hstat]
      exact hw
    have : PreservesColimit (span g f)
        (MonoidalCategory.tensorRight (Δ[1] : SSet.{u})) := inferInstance
    have sq_tensor : IsPushout (g ▷ (Δ[1] : SSet.{u})) (f ▷ (Δ[1] : SSet.{u}))
        (f' ▷ (Δ[1] : SSet.{u})) (g' ▷ (Δ[1] : SSet.{u})) :=
      (MonoidalCategory.tensorRight (Δ[1] : SSet.{u})).map_isPushout sq
    let H' : B' ⊗ (Δ[1] : SSet.{u}) ⟶ B' :=
      sq_tensor.desc h_B h_A' h_glue
    have h_B_eq : (f' ▷ (Δ[1] : SSet.{u})) ≫ H' = h_B :=
      sq_tensor.inl_desc h_B h_A' h_glue
    have h_A'_eq : (g' ▷ (Δ[1] : SSet.{u})) ≫ H' = h_A' :=
      sq_tensor.inr_desc h_B h_A' h_glue
    have h₀ : SSet.ι₀ (X := B') ≫ H' = 𝟙 B' := by
      apply sq.hom_ext
      · calc f' ≫ (SSet.ι₀ ≫ H') = (f' ≫ SSet.ι₀) ≫ H' := by rw [Category.assoc]
          _ = (SSet.ι₀ ≫ (f' ▷ (Δ[1] : SSet.{u}))) ≫ H' := by rw [← SSet.ι₀_comp]
          _ = SSet.ι₀ ≫ ((f' ▷ (Δ[1] : SSet.{u})) ≫ H') := by rw [Category.assoc]
          _ = SSet.ι₀ ≫ h_B := by rw [h_B_eq]
          _ = SSet.ι₀ ≫ (fst B (Δ[1] : SSet.{u}) ≫ f') := rfl
          _ = (SSet.ι₀ ≫ fst B (Δ[1] : SSet.{u})) ≫ f' := by rw [Category.assoc]
          _ = 𝟙 B ≫ f' := by rw [SSet.ι₀_fst]
          _ = f' := by rw [Category.id_comp]
          _ = f' ≫ 𝟙 B' := by rw [Category.comp_id]
      · calc g' ≫ (SSet.ι₀ ≫ H') = (g' ≫ SSet.ι₀) ≫ H' := by rw [Category.assoc]
          _ = (SSet.ι₀ ≫ (g' ▷ (Δ[1] : SSet.{u}))) ≫ H' := by rw [← SSet.ι₀_comp]
          _ = SSet.ι₀ ≫ ((g' ▷ (Δ[1] : SSet.{u})) ≫ H') := by rw [Category.assoc]
          _ = SSet.ι₀ ≫ h_A' := by rw [h_A'_eq]
          _ = SSet.ι₀ ≫ (w.homotopy.h ≫ g') := rfl
          _ = (SSet.ι₀ ≫ w.homotopy.h) ≫ g' := by rw [Category.assoc]
          _ = 𝟙 A' ≫ g' := by rw [w.homotopy.h₀]
          _ = g' := by rw [Category.id_comp]
          _ = g' ≫ 𝟙 B' := by rw [Category.comp_id]
    have h₁ : SSet.ι₁ (X := B') ≫ H' = r' ≫ f' := by
      apply sq.hom_ext
      · calc f' ≫ (SSet.ι₁ ≫ H') = (f' ≫ SSet.ι₁) ≫ H' := by rw [Category.assoc]
          _ = (SSet.ι₁ ≫ (f' ▷ (Δ[1] : SSet.{u}))) ≫ H' := by rw [← SSet.ι₁_comp]
          _ = SSet.ι₁ ≫ ((f' ▷ (Δ[1] : SSet.{u})) ≫ H') := by rw [Category.assoc]
          _ = SSet.ι₁ ≫ h_B := by rw [h_B_eq]
          _ = SSet.ι₁ ≫ (fst B (Δ[1] : SSet.{u}) ≫ f') := rfl
          _ = (SSet.ι₁ ≫ fst B (Δ[1] : SSet.{u})) ≫ f' := by rw [Category.assoc]
          _ = 𝟙 B ≫ f' := by rw [SSet.ι₁_fst]
          _ = (f' ≫ r') ≫ f' := by rw [← hr']
          _ = f' ≫ (r' ≫ f') := by rw [Category.assoc]
      · calc g' ≫ (SSet.ι₁ ≫ H') = (g' ≫ SSet.ι₁) ≫ H' := by rw [Category.assoc]
          _ = (SSet.ι₁ ≫ (g' ▷ (Δ[1] : SSet.{u}))) ≫ H' := by rw [← SSet.ι₁_comp]
          _ = SSet.ι₁ ≫ ((g' ▷ (Δ[1] : SSet.{u})) ≫ H') := by rw [Category.assoc]
          _ = SSet.ι₁ ≫ h_A' := by rw [h_A'_eq]
          _ = SSet.ι₁ ≫ (w.homotopy.h ≫ g') := rfl
          _ = (SSet.ι₁ ≫ w.homotopy.h) ≫ g' := by rw [Category.assoc]
          _ = (w.r ≫ f) ≫ g' := by rw [w.homotopy.h₁]
          _ = w.r ≫ (f ≫ g') := by rw [Category.assoc]
          _ = w.r ≫ (g ≫ f') := by rw [← sq.w]
          _ = (w.r ≫ g) ≫ f' := by rw [Category.assoc]
          _ = (g' ≫ r') ≫ f' := by rw [← hg']
          _ = g' ≫ (r' ≫ f') := by rw [Category.assoc]
    have h_stationary : ∀ {n : SimplexCategoryᵒᵖ} (x : B'.obj n)
        (hx : x ∈ (Subcomplex.range f').obj n) (t : (Δ[1] : SSet.{u}).obj n),
          H'.app n ⟨x, t⟩ = x := by
      intro n x hx t
      simp only [Subcomplex.range, Subfunctor.range_obj, Set.mem_range] at hx
      obtain ⟨b, hb⟩ := hx
      have hb' : f'.app n b = x := hb
      calc H'.app n ⟨x, t⟩ = H'.app n ⟨f'.app n b, t⟩ := by rw [← hb]
        _ = H'.app n ((f' ▷ (Δ[1] : SSet.{u})).app n ⟨b, t⟩) := by
            rfl
        _ = ((f' ▷ (Δ[1] : SSet.{u})) ≫ H').app n ⟨b, t⟩ := by
            rfl
        _ = h_B.app n ⟨b, t⟩ := by
            have h_eq : ((f' ▷ (Δ[1] : SSet.{u})) ≫ H').app n ⟨b, t⟩ = h_B.app n ⟨b, t⟩ :=
              congr_fun (congr_arg (fun h => h.app n) h_B_eq) ⟨b, t⟩
            exact h_eq
        _ = (fst B (Δ[1] : SSet.{u}) ≫ f').app n ⟨b, t⟩ := rfl
        _ = f'.app n ((fst B (Δ[1] : SSet.{u})).app n ⟨b, t⟩) := by
            rfl
        _ = f'.app n b := by
            rfl
        _ = x := hb
    exact ⟨⟨r', hr', ⟨H', h₀, h₁, fun {n} x hx t => h_stationary (n := n) x hx t⟩⟩⟩

/-! ## Mapping-path space

For `f : X ⟶ Y`, the mapping-path space is the pullback
`X ×_Y pathSpace Y` along `f` and `eval₀ : pathSpace Y ⟶ Y`.
It comes with a section `X ⟶ mappingPathSpace f` and retraction
`mappingPathSpace f ⟶ X`. Reuses `SSet.pathSpace`, `SSet.constPath`,
`SSet.eval₀` without duplication. -/

noncomputable def mappingPathSpace {X Y : SSet.{u}} (f : X ⟶ Y) : SSet.{u} :=
  pullback f (SSet.eval₀ (X := Y))

noncomputable def mappingPathSection {X Y : SSet.{u}} (f : X ⟶ Y) :
    X ⟶ mappingPathSpace (f := f) :=
  pullback.lift (𝟙 X) (f ≫ Y.constPath) (by
    simp [SSet.eval₀_constPath])

noncomputable def mappingPathRetract {X Y : SSet.{u}} (f : X ⟶ Y) :
    mappingPathSpace (f := f) ⟶ X :=
  pullback.fst f (SSet.eval₀ (X := Y))

noncomputable def mappingPathEval {X Y : SSet.{u}} (f : X ⟶ Y) :
    mappingPathSpace (f := f) ⟶ SSet.pathSpace (X := Y) :=
  pullback.snd f (SSet.eval₀ (X := Y))

@[simp]
lemma mappingPathSection_comp_retract {X Y : SSet.{u}} (f : X ⟶ Y) :
    mappingPathSection f ≫ mappingPathRetract f = 𝟙 X := by
  simp only [mappingPathSection, mappingPathRetract]
  exact pullback.lift_fst _ _ _

lemma mappingPathSection_comp_eval {X Y : SSet.{u}} (f : X ⟶ Y) :
    mappingPathSection f ≫ mappingPathEval f = f ≫ Y.constPath := by
  simp only [mappingPathSection, mappingPathEval]
  exact pullback.lift_snd _ _ _

lemma mappingPathSection_comp_fst {X Y : SSet.{u}} (f : X ⟶ Y) :
    mappingPathSection f ≫ pullback.fst f (SSet.eval₀ (X := Y)) = 𝟙 X := by
  simp only [mappingPathSection]
  exact pullback.lift_fst _ _ _

/-! ## Cylinder

The generating cylinder inclusion
`∂Δ[n] ⊗ Δ[1] ∪ Δ[n] ⊗ {0} ↪ Δ[n] ⊗ Δ[1]` as
`(boundary n).unionProd (face {0})`. This is the SSet analogue of
the topological cylinder inclusion and the reusable HEP (homotopy extension)
input. Its already proved anodyne property, obtained from the pushout-product
theorem `anodyneExtensions_unionProd_ι` via the horn `Δ[0] → Δ[1]`
(i.e. `face {0}`), is the reusable HEP input, without invoking `W`. -/

noncomputable def cylinderSubcomplex (n : ℕ) :
    (Δ[n] ⊗ (Δ[1] : SSet.{u})).Subcomplex :=
  (SSet.boundary n).unionProd (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex)

noncomputable def cylinderInclusion (n : ℕ) :
    (cylinderSubcomplex (n : ℕ) : SSet.{u}) ⟶ (Δ[n] ⊗ (Δ[1] : SSet.{u})) :=
  (cylinderSubcomplex (n : ℕ)).ι

theorem cylinderInclusion_mem_anodyneExtensions (n : ℕ) :
    SSet.anodyneExtensions.{u} (SSet.cylinderInclusion (n := n)) := by
  have h_face : SSet.anodyneExtensions.{u}
      (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι := by
    have h_eq : (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex) =
        SSet.horn (n := 1) (0 : Fin 2) := by
      have h_fin : ({0} : Finset (Fin 2)) = {1}ᶜ := by decide
      calc (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex)
          = SSet.stdSimplex.face ({1}ᶜ : Finset (Fin 2)) := by rw [h_fin]
        _ = SSet.horn (n := 1) (0 : Fin 2) := by
            ext m x
            simp [SSet.horn_eq_iSup]
    rw [h_eq]
    exact SSet.anodyneExtensions.horn_ι (0 : Fin 2)
  have h : SSet.anodyneExtensions.{u}
      ((SSet.boundary n).unionProd
        (SSet.stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex)).ι :=
    SSet.anodyneExtensions_unionProd_ι (SSet.boundary n) _ h_face
  simpa [SSet.cylinderInclusion, SSet.cylinderSubcomplex] using h

end SSet

/-! ## Remaining exact lemmas (second packet, not claimed in this file)

The following are *not* proved in this first scaffold-free packet.
They are listed explicitly as required follow-up work, separated to avoid
circular use of `trivialFibration_iff` or filtered-colimit stability.
`IsStableUnderCobaseChange strongDeformationRetract` is proved above via
`Limits.IsPushout` and `⊗ Δ[1]` preserving colimits (cartesian closedness).

Nonclaim: the cylinder inclusion
`∂Δ[n] ⊗ Δ[1] ∪ Δ[n] ⊗ {0} ↪ Δ[n] ⊗ Δ[1]` is not in general a simplicial
strong deformation retract (e.g. `n = 1`: the subcomplex contains every vertex
of `Δ[1] × Δ[1]` but omits the top edge, so no simplicial retraction fixing
all vertices can exist; `n = 0` endpoint orientation also fails via monotone
interval maps). Future work must therefore use its already proved anodyne
property from the pushout-product theorem, not attempt
`cylinderInclusion_isStrongDeformationRetract` nor the dependent
`strongDeformationRetract_mono_isAnodyne_of_cylinder`.

Remaining work:

1. `theorem subsingleton_π_fiber_of_W_fibration {f : X ⟶ Y} [KanComplex X]
     [KanComplex Y] [Fibration f] (hf : W f) (y) (n) (x) :
     Subsingleton (π n (fiber f y) x)` — uses LES from
   `FibrationSequence`/`ConnectingExactness` + `W`'s `π`-bijectivity +
   `isFibrant_fiber`; reuses `π.map` naturality. No colimits.

2. `theorem KanComplex.W.hasLiftingPropertyFixedTop {X Y} {f : X ⟶ Y}
     [KanComplex X] [KanComplex Y] [Fibration f] (hf : W f) {n}
     (top : SSet.boundary n ⟶ X) : HasLiftingPropertyFixedTop (SSet.boundary n).ι f top`
   (equivalently `HasLiftingProperty ((boundary n).unionProd (face {0})).ι f`
   after adjunction). Proof reduces via `unionProd.isPushout` to
   sphere-filling in `fiber f y` using (1) instead of `I.rlp`.

3. Packet-2 stability (separated, gated on colimit lane):
   `horn_memW`, `anodyneExtensions_le_W`, and downstream
   `trivialFibration_iff` converse via `anodyne ≤ W` + 2/3 + retract
   argument and small-object factorization. Requires
   `W.isStableUnderFilteredColimits` / `IsStableAnodyne`.

No `ModelCategory SSet`, no `W.IsStableUnderFilteredColimits`,
no `anodyne = trivialCofibrations`, no `trivialFibration_iff` proof are
claimed in this file.
-/
