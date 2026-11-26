/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Comonad.Comodule

/-!
# Two-sided comonadic cobar degrees and operators

Let `G` be a comonad on `C`, let `R : C ⥤ D` have right coaction `R ⟶ G ⋙ R`, and let `L : A ⥤
C` have left coaction `L ⟶ L ⋙ G`. The degree-`n` cobar functor is `a ↦ R(G^n(L(a)))`, with
powers `G^0 = 𝟭 C` and `G^(n+1) = G ⋙ G^n`.

Coface zero uses the iterated right coaction, the last coface uses the left coaction, and
interior cofaces insert comultiplication. Codegeneracies insert the counit. The cobar indices
count from the right-comodule end; `Fin.rev` relates them to insertion indices counted from
the left-comodule end. All operators are natural in `a`, with independent category and
morphism universes for `A`, `C`, and `D`.

Reference: the categorical dual of the two-sided bar construction in J. P. May, *The Geometry
of Iterated Loop Spaces*, Lecture Notes in Mathematics 271, Springer, 1972, Chapter 9,
Construction 9.6 and Remark 9.12, <https://doi.org/10.1007/BFb0067491>.
-/

@[expose] public section

namespace CategoryTheory
namespace Comonad

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {A : Type u₃} [Category.{v₃} A]

/-- The iterated powers of a comonad functor.

Set `G^0 = 𝟭 C` and `G^(n+1) = G ⋙ G^n` for a comonad `G` on `C`. -/
abbrev comonadPow (G : Comonad C) : ℕ → C ⥤ C
| 0 => 𝟭 C
| n + 1 => (G : C ⥤ C) ⋙ comonadPow G n

/-- The identity power of a comonad.

The zeroth comonad power is the identity functor. -/
@[simp] lemma comonadPow_zero (G : Comonad C) : comonadPow G 0 = 𝟭 C := rfl

/-- The successor formula for a comonad power.

The power `G^(n+1)` is `G ⋙ G^n`. -/
@[simp] lemma comonadPow_succ (G : Comonad C) (n : ℕ) :
    comonadPow G (n + 1) = (G : C ⥤ C) ⋙ comonadPow G n := rfl

/-- Commutation of a comonad power with one objectwise application.

For `X ∈ C`, the objects `G^n(G(X))` and `G(G^n(X))` are equal for the specified power
recursion. -/
theorem comonadPow_obj_G_comm (G : Comonad C) (n : ℕ) (X : C) :
    (comonadPow G n).obj (G.toFunctor.obj X) =
      G.toFunctor.obj ((comonadPow G n).obj X) := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih => exact ih (G.toFunctor.obj X)

/-- The object formula for a successor comonad power.

The object `G^(n+1)(X)` is `G(G^n(X))`. -/
theorem comonadPow_succ_obj_eq (G : Comonad C) (n : ℕ) (X : C) :
    (comonadPow G (n + 1)).obj X = G.toFunctor.obj ((comonadPow G n).obj X) :=
  comonadPow_obj_G_comm G n X

/-- Comultiplication insertion at a comonad-power position.

For `i : Fin n`, insert `δ` into `G^n(X)` to obtain `G^(n+1)(X)`. Position zero is the
innermost insertion near the left-comodule object; later positions recurse at `G(X)`. -/
noncomputable def deltaAtPos (G : Comonad C) : (n : ℕ) → (i : Fin n) → (X : C) →
    (comonadPow G n).obj X ⟶ (comonadPow G (n + 1)).obj X
| 0, i, _ => nomatch i
| n + 1, ⟨0, _⟩, X => (comonadPow G n).map (G.δ.app X)
| n + 1, ⟨k + 1, hk⟩, X => deltaAtPos G n ⟨k, by omega⟩ (G.toFunctor.obj X)

/-- Naturality of comultiplication insertion.

For every position `i`, the insertion `G^n(X) → G^(n+1)(X)` commutes with the corresponding
powers of a morphism `X → Y`. -/
lemma deltaAtPos_naturality (G : Comonad C) (n : ℕ) (k : Fin n) {X Y : C}
    (f : X ⟶ Y) :
    (comonadPow G n).map f ≫ deltaAtPos G n k Y =
    deltaAtPos G n k X ≫ (comonadPow G (n + 1)).map f := by
  induction n generalizing X Y with
  | zero => exact isEmptyElim k
  | succ n ih =>
    match k with
    | ⟨0, _⟩ =>
      have h1 : (comonadPow G (n + 1 + 1)).map f =
          (comonadPow G n).map (G.toFunctor.map (G.toFunctor.map f)) := rfl
      have h2 : (comonadPow G (n + 1)).map f =
          (comonadPow G n).map (G.toFunctor.map f) := rfl
      simp only [deltaAtPos] at *
      rw [h1, h2]
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      exact G.δ.naturality f
    | ⟨k + 1, hk⟩ =>
      simp only [deltaAtPos]
      exact ih ⟨k, by omega⟩ (G.toFunctor.map f)

/-- Counit insertion at a comonad-power position.

For `i : Fin (n+1)`, insert `ε` into `G^(n+1)(X)` to obtain `G^n(X)`, counting positions from
the left-comodule end. -/
noncomputable def epsilonAtPos (G : Comonad C) : (n : ℕ) → (i : Fin (n + 1)) →
    (X : C) → (comonadPow G (n + 1)).obj X ⟶ (comonadPow G n).obj X
| 0, _, X => G.ε.app X
| n + 1, ⟨0, _⟩, X => (comonadPow G (n + 1)).map (G.ε.app X)
| n + 1, ⟨k + 1, hk⟩, X => epsilonAtPos G n ⟨k, by omega⟩ (G.toFunctor.obj X)

/-- Naturality of counit insertion.

For every insertion position, counit contraction commutes with the powers of a carrier
morphism `X → Y`. -/
lemma epsilonAtPos_naturality (G : Comonad C) (n : ℕ) (i : Fin (n + 1)) {X Y : C}
    (f : X ⟶ Y) :
    (comonadPow G (n + 1)).map f ≫ epsilonAtPos G n i Y =
    epsilonAtPos G n i X ≫ (comonadPow G n).map f := by
  induction n generalizing X Y with
  | zero =>
    simp only [epsilonAtPos]
    exact G.ε.naturality f
  | succ n ih =>
    match i with
    | ⟨0, _⟩ =>
      have hε : G.toFunctor.map f ≫ G.ε.app Y = G.ε.app X ≫ f :=
        G.ε.naturality f
      calc
        (comonadPow G (n + 1 + 1)).map f ≫
            (comonadPow G (n + 1)).map (G.ε.app Y)
            = (comonadPow G n).map (G.toFunctor.map (G.toFunctor.map f)) ≫
              (comonadPow G n).map (G.toFunctor.map (G.ε.app Y)) := rfl
        _ = (comonadPow G n).map (G.toFunctor.map (G.toFunctor.map f) ≫
              G.toFunctor.map (G.ε.app Y)) := by
          rw [← (comonadPow G n).map_comp]
        _ = (comonadPow G n).map
              (G.toFunctor.map (G.toFunctor.map f ≫ G.ε.app Y)) := by
          rw [← Functor.map_comp]
        _ = (comonadPow G n).map (G.toFunctor.map (G.ε.app X ≫ f)) := by
          rw [hε]
        _ = (comonadPow G n).map (G.toFunctor.map (G.ε.app X) ≫
              G.toFunctor.map f) := by
          rw [Functor.map_comp]
        _ = (comonadPow G n).map (G.toFunctor.map (G.ε.app X)) ≫
              (comonadPow G n).map (G.toFunctor.map f) := by
          rw [Functor.map_comp]
        _ = (comonadPow G (n + 1)).map (G.ε.app X) ≫
              (comonadPow G (n + 1)).map f := rfl
    | ⟨k + 1, hk⟩ =>
      simp only [epsilonAtPos]
      exact ih ⟨k, by omega⟩ (G.toFunctor.map f)

/-- The right-end indexing of an interior cobar coface.

The interior coface insertion at `i : Fin n` is the comultiplication insertion at the reversed
position `i.rev`. -/
noncomputable def cobarDeltaAtPos (G : Comonad C) (n : ℕ) (i : Fin n) (X : C) :
    (comonadPow G n).obj X ⟶ (comonadPow G (n + 1)).obj X :=
  deltaAtPos G n i.rev X

/-- The right-end indexing of a cobar codegeneracy.

The codegeneracy insertion at `i : Fin (n+1)` is the counit insertion at the reversed position
`i.rev`. -/
noncomputable def cobarEpsilonAtPos (G : Comonad C) (n : ℕ) (i : Fin (n + 1))
    (X : C) :
    (comonadPow G (n + 1)).obj X ⟶ (comonadPow G n).obj X :=
  epsilonAtPos G n i.rev X

/-- The reversed-position formula for cobar comultiplication insertion.

The right-end insertion at `i` equals the comultiplication insertion at `i.rev` in left-end
indexing. -/
@[simp] lemma cobarDeltaAtPos_rev (G : Comonad C) (n : ℕ) (i : Fin n) (X : C) :
    cobarDeltaAtPos G n i X = deltaAtPos G n i.rev X := rfl

/-- The reversed-position formula for cobar counit insertion.

The right-end contraction at `i` equals the counit insertion at `i.rev` in left-end indexing. -/
@[simp] lemma cobarEpsilonAtPos_rev (G : Comonad C) (n : ℕ) (i : Fin (n + 1))
    (X : C) :
    cobarEpsilonAtPos G n i X = epsilonAtPos G n i.rev X := rfl

/-- Naturality of right-indexed cobar comultiplication.

The reversed-position comultiplication insertion commutes with powers of each morphism in the
comonad's carrier category. -/
lemma cobarDeltaAtPos_naturality (G : Comonad C) (n : ℕ) (i : Fin n) {X Y : C}
    (f : X ⟶ Y) :
    (comonadPow G n).map f ≫ cobarDeltaAtPos G n i Y =
    cobarDeltaAtPos G n i X ≫ (comonadPow G (n + 1)).map f := by
  simp only [cobarDeltaAtPos]
  exact deltaAtPos_naturality G n i.rev f

/-- Naturality of right-indexed cobar counit contraction.

The reversed-position counit insertion commutes with powers of each morphism in the comonad's
carrier category. -/
lemma cobarEpsilonAtPos_naturality (G : Comonad C) (n : ℕ) (i : Fin (n + 1))
    {X Y : C} (f : X ⟶ Y) :
    (comonadPow G (n + 1)).map f ≫ cobarEpsilonAtPos G n i Y =
    cobarEpsilonAtPos G n i X ≫ (comonadPow G n).map f := by
  simp only [cobarEpsilonAtPos]
  exact epsilonAtPos_naturality G n i.rev f

section Elementary

variable {G : Comonad C} {R : RightComodule G D} {L : LeftComodule A G}

/-- The functor in one degree of a two-sided comonadic cobar construction.

For a right comodule `R : C ⥤ D` and left comodule `L : A ⥤ C`, degree `n` is `(L ⋙ G^n) ⋙ R :
A ⥤ D`. -/
abbrev cobarObj (G : Comonad C) (R : RightComodule G D) (L : LeftComodule A G)
    (n : ℕ) : A ⥤ D :=
  (L.functor ⋙ comonadPow G n) ⋙ R.functor

/-- The object formula for a two-sided cobar degree.

At `a ∈ A`, degree `n` has value `R(G^n(L(a)))`. -/
@[simp] lemma cobarObj_obj (G : Comonad C) (R : RightComodule G D)
    (L : LeftComodule A G) (n : ℕ) (a : A) :
    (cobarObj G R L n).obj a =
      R.functor.obj ((comonadPow G n).obj (L.functor.obj a)) := rfl

/-- The carrier-morphism formula for a two-sided cobar degree.

A morphism `f : a → b` maps to `R.map(G^n.map(L.map(f)))`. -/
@[simp] lemma cobarObj_map {G : Comonad C} {R : RightComodule G D}
    {L : LeftComodule A G} {n : ℕ} {a b : A} (f : a ⟶ b) :
    (cobarObj G R L n).map f =
      R.functor.map ((comonadPow G n).map (L.functor.map f)) := rfl

/-- The degree-zero two-sided cobar functor.

Degree zero is the composite `L ⋙ R` of the two underlying comodule functors. -/
@[simp] lemma cobarObj_zero (G : Comonad C) (R : RightComodule G D)
    (L : LeftComodule A G) :
    cobarObj G R L 0 = L.functor ⋙ R.functor := rfl

/-- The iterated right-comodule coaction.

The coaction gives `R(G^n(X)) → R(G^(n+1)(X))`, starting with the right coaction at `X` and
defining the next degree by the preceding map at `G(X)`. -/
noncomputable def rightCoactionPow (G : Comonad C) (R : RightComodule G D) :
    (n : ℕ) → (X : C) → R.functor.obj ((comonadPow G n).obj X) ⟶
      R.functor.obj ((comonadPow G (n + 1)).obj X)
| 0, X => R.coaction.app X
| n + 1, X => rightCoactionPow G R n (G.toFunctor.obj X)

/-- The zeroth iterated right-comodule coaction.

The degree-zero iterated coaction is the right comodule coaction `R(X) → R(G(X))`. -/
@[simp] lemma rightCoactionPow_zero (G : Comonad C) (R : RightComodule G D)
    (X : C) :
    rightCoactionPow G R 0 X = R.coaction.app X := rfl

/-- The successor formula for iterated right coaction.

The degree-`n+1` iterated right coaction at `X` is the degree-`n` iterated coaction at `G(X)`. -/
@[simp] lemma rightCoactionPow_succ (G : Comonad C) (R : RightComodule G D)
    (n : ℕ) (X : C) :
    rightCoactionPow G R (n + 1) X =
      rightCoactionPow G R n (G.toFunctor.obj X) := rfl

/-- Naturality of iterated right-comodule coaction.

The iterated coaction commutes with the maps `R(G^n(f))` and `R(G^(n+1)(f))` of every carrier
morphism. -/
lemma rightCoactionPow_naturality (G : Comonad C) (R : RightComodule G D)
    (n : ℕ) {X Y : C} (f : X ⟶ Y) :
    R.functor.map ((comonadPow G n).map f) ≫ rightCoactionPow G R n Y =
    rightCoactionPow G R n X ≫
      R.functor.map ((comonadPow G (n + 1)).map f) := by
  induction n generalizing X Y with
  | zero =>
    simp only [rightCoactionPow]
    exact R.coaction.naturality f
  | succ n ih =>
    simp only [rightCoactionPow]
    exact ih (X := G.toFunctor.obj X) (Y := G.toFunctor.obj Y)
      (f := G.toFunctor.map f)

/-- The component of a two-sided cobar coface.

At `a`, coface zero is the iterated right coaction, coface `n+1` is
`R.map(G^n.map(L.coaction.app a))`, and each interior coface is the reversed-position
comultiplication insertion mapped by `R`. -/
noncomputable def cobarCofaceApp (n : ℕ) (i : Fin (n + 2)) (a : A) :
    (cobarObj G R L n).obj a ⟶ (cobarObj G R L (n + 1)).obj a :=
  if h0 : i.val = 0 then
    rightCoactionPow G R n (L.functor.obj a)
  else if hlast : i.val = n + 1 then
    R.functor.map ((comonadPow G n).map (L.coaction.app a))
  else
    have hi : i.val < n + 2 := i.isLt
    have hk : i.val - 1 < n := by
      have h0' : 0 < i.val := by omega
      have hle : i.val ≤ n := by omega
      omega
    R.functor.map (cobarDeltaAtPos G n ⟨i.val - 1, hk⟩ (L.functor.obj a))

/-- The natural coface between two-sided cobar degree functors.

For `i : Fin (n+2)`, the endpoint coactions and interior comultiplication insertions define a
natural transformation from degree `n` to degree `n+1`. -/
noncomputable def cobarCoface (n : ℕ) (i : Fin (n + 2)) :
    cobarObj G R L n ⟶ cobarObj G R L (n + 1) where
  app a := cobarCofaceApp n i a
  naturality a b f := by
    have hF : (cobarObj G R L n).map f =
        R.functor.map ((comonadPow G n).map (L.functor.map f)) := rfl
    have hG : (cobarObj G R L (n + 1)).map f =
        R.functor.map ((comonadPow G (n + 1)).map (L.functor.map f)) := rfl
    by_cases h0 : i.val = 0
    · have ha : cobarCofaceApp n i a =
          rightCoactionPow G R n (L.functor.obj a) := by
        unfold cobarCofaceApp
        rw [dite_eq_left h0]
      have hb : cobarCofaceApp n i b =
          rightCoactionPow G R n (L.functor.obj b) := by
        unfold cobarCofaceApp
        rw [dite_eq_left h0]
      rw [ha, hb, hF, hG]
      exact rightCoactionPow_naturality G R n (L.functor.map f)
    · by_cases hlast : i.val = n + 1
      · have ha : cobarCofaceApp n i a =
            R.functor.map ((comonadPow G n).map (L.coaction.app a)) := by
          unfold cobarCofaceApp
          rw [dite_eq_right h0, dite_eq_left hlast]
        have hb : cobarCofaceApp n i b =
            R.functor.map ((comonadPow G n).map (L.coaction.app b)) := by
          unfold cobarCofaceApp
          rw [dite_eq_right h0, dite_eq_left hlast]
        rw [ha, hb, hF, hG]
        apply Eq.symm
        have hL : L.coaction.app a ≫ G.toFunctor.map (L.functor.map f) =
            L.functor.map f ≫ L.coaction.app b :=
          (L.coaction.naturality f).symm
        have h1 : (comonadPow G (n + 1)).map (L.functor.map f) =
            (comonadPow G n).map (G.toFunctor.map (L.functor.map f)) := rfl
        calc
          R.functor.map ((comonadPow G n).map (L.coaction.app a)) ≫
              R.functor.map ((comonadPow G (n + 1)).map (L.functor.map f))
              = R.functor.map ((comonadPow G n).map (L.coaction.app a)) ≫
                R.functor.map ((comonadPow G n).map
                  (G.toFunctor.map (L.functor.map f))) := by
            rw [h1]
          _ = R.functor.map ((comonadPow G n).map (L.coaction.app a) ≫
                  (comonadPow G n).map
                    (G.toFunctor.map (L.functor.map f))) := by
            rw [← R.functor.map_comp]
          _ = R.functor.map ((comonadPow G n).map (L.coaction.app a ≫
                  G.toFunctor.map (L.functor.map f))) := by
            rw [← (comonadPow G n).map_comp]
          _ = R.functor.map ((comonadPow G n).map
                  (L.functor.map f ≫ L.coaction.app b)) := by
            rw [hL]
          _ = R.functor.map ((comonadPow G n).map (L.functor.map f) ≫
                  (comonadPow G n).map (L.coaction.app b)) := by
            rw [(comonadPow G n).map_comp]
          _ = R.functor.map ((comonadPow G n).map (L.functor.map f)) ≫
                  R.functor.map ((comonadPow G n).map (L.coaction.app b)) := by
            rw [R.functor.map_comp]
      · have hk : i.val - 1 < n := by omega
        let k : Fin n := ⟨i.val - 1, hk⟩
        have ha : cobarCofaceApp n i a =
            R.functor.map (cobarDeltaAtPos G n k (L.functor.obj a)) := by
          unfold cobarCofaceApp
          rw [dite_eq_right h0, dite_eq_right hlast]
        have hb : cobarCofaceApp n i b =
            R.functor.map (cobarDeltaAtPos G n k (L.functor.obj b)) := by
          unfold cobarCofaceApp
          rw [dite_eq_right h0, dite_eq_right hlast]
        rw [ha, hb, hF, hG]
        apply Eq.symm
        have hδ := cobarDeltaAtPos_naturality G n k (f := L.functor.map f)
        calc
          R.functor.map (cobarDeltaAtPos G n k (L.functor.obj a)) ≫
              R.functor.map ((comonadPow G (n + 1)).map (L.functor.map f))
              = R.functor.map (cobarDeltaAtPos G n k (L.functor.obj a) ≫
                  (comonadPow G (n + 1)).map (L.functor.map f)) := by
            rw [← R.functor.map_comp]
          _ = R.functor.map ((comonadPow G n).map (L.functor.map f) ≫
                  cobarDeltaAtPos G n k (L.functor.obj b)) := by
            rw [← hδ]
          _ = R.functor.map ((comonadPow G n).map (L.functor.map f)) ≫
                  R.functor.map (cobarDeltaAtPos G n k (L.functor.obj b)) := by
            rw [R.functor.map_comp]

/-- The right-end component of a cobar coface.

The zeroth coface at `a` is the iterated right coaction on `R(G^n(L(a)))`. -/
@[simp] lemma cobarCofaceApp_right (n : ℕ) (a : A) :
    cobarCofaceApp n ⟨0, by omega⟩ a =
      rightCoactionPow G R n (L.functor.obj a) := rfl

/-- The zeroth cobar coface as a natural-transformation component.

The component of coface zero is the iterated right-comodule coaction. -/
@[simp] lemma cobarCoface_right (n : ℕ) (a : A) :
    (cobarCoface n ⟨0, by omega⟩).app a =
      rightCoactionPow G R n (L.functor.obj a) := rfl

/-- The left-end component of a cobar coface.

The final coface at `a` is `R.map(G^n.map(L.coaction.app a))`. -/
@[simp] lemma cobarCofaceApp_left (n : ℕ) (a : A) :
    cobarCofaceApp n ⟨n + 1, by omega⟩ a =
      R.functor.map ((comonadPow G n).map (L.coaction.app a)) := by
  have h0 : ¬ ((⟨n + 1, by omega⟩ : Fin (n + 2)).val = 0) := by simp
  have hlast : ((⟨n + 1, by omega⟩ : Fin (n + 2)).val = n + 1) := rfl
  unfold cobarCofaceApp
  rw [dite_eq_right h0, dite_eq_left hlast]

/-- The final cobar coface as a natural-transformation component.

The component of coface `n+1` is the left-comodule coaction mapped through `G^n` and `R`. -/
@[simp] lemma cobarCoface_left (n : ℕ) (a : A) :
    (cobarCoface n ⟨n + 1, by omega⟩).app a =
      R.functor.map ((comonadPow G n).map (L.coaction.app a)) := by
  change cobarCofaceApp n ⟨n + 1, by omega⟩ a = _
  rw [cobarCofaceApp_left]

/-- The interior component of a cobar coface.

For `i : Fin n`, coface `i+1` inserts comultiplication at left-end position `i.rev`, then
applies `R`. -/
@[simp] lemma cobarCofaceApp_middle (n : ℕ) (i : Fin n) (a : A) :
    cobarCofaceApp n
        ⟨i.val + 1,
          Nat.lt_trans (Nat.succ_lt_succ i.isLt) (Nat.lt_succ_self _)⟩ a =
      R.functor.map (cobarDeltaAtPos G n i (L.functor.obj a)) := by
  have hi := i.isLt
  have h0 : ¬ ((⟨i.val + 1,
      Nat.lt_trans (Nat.succ_lt_succ hi) (Nat.lt_succ_self _)⟩ :
      Fin (n + 2)).val = 0) := by
    simp
  have hlast : ¬ ((⟨i.val + 1,
      Nat.lt_trans (Nat.succ_lt_succ hi) (Nat.lt_succ_self _)⟩ :
      Fin (n + 2)).val = n + 1) := by
    intro h
    have hle : i.val + 1 ≤ n := Nat.succ_le_of_lt hi
    have hlt : i.val + 1 < n + 1 :=
      Nat.lt_of_le_of_lt hle (Nat.lt_succ_self n)
    exact Nat.ne_of_lt hlt h
  have hk_eq : (⟨(⟨i.val + 1,
      Nat.lt_trans (Nat.succ_lt_succ hi) (Nat.lt_succ_self _)⟩ :
      Fin (n + 2)).val - 1, hi⟩ : Fin n) = i := by
    apply Fin.ext
    simp
  simp only [cobarCofaceApp, dite_eq_right h0, dite_eq_right hlast, hk_eq]

/-- An interior cobar coface as a natural-transformation component.

The component of coface `i+1` is `R` applied to the right-indexed comultiplication insertion
at `i`. -/
@[simp] lemma cobarCoface_middle (n : ℕ) (i : Fin n) (a : A) :
    (cobarCoface n ⟨i.val + 1,
        Nat.lt_trans (Nat.succ_lt_succ i.isLt) (Nat.lt_succ_self _)⟩).app a =
      R.functor.map (cobarDeltaAtPos G n i (L.functor.obj a)) := by
  simp only [cobarCoface, cobarCofaceApp_middle]

/-- The natural codegeneracy of two-sided cobar degree functors.

For `i : Fin (n+1)`, counit insertion at reversed position `i.rev`, followed by `R`, gives a
natural map from degree `n+1` to degree `n`. -/
noncomputable def cobarCodegeneracy (n : ℕ) (i : Fin (n + 1)) :
    cobarObj G R L (n + 1) ⟶ cobarObj G R L n where
  app a := R.functor.map (cobarEpsilonAtPos G n i (L.functor.obj a))
  naturality a b f := by
    have hF : (cobarObj G R L (n + 1)).map f =
        R.functor.map ((comonadPow G (n + 1)).map (L.functor.map f)) := rfl
    have hG : (cobarObj G R L n).map f =
        R.functor.map ((comonadPow G n).map (L.functor.map f)) := rfl
    rw [hF, hG]
    apply Eq.symm
    have hε := cobarEpsilonAtPos_naturality G n i (f := L.functor.map f)
    calc
      R.functor.map (cobarEpsilonAtPos G n i (L.functor.obj a)) ≫
          R.functor.map ((comonadPow G n).map (L.functor.map f))
          = R.functor.map (cobarEpsilonAtPos G n i (L.functor.obj a) ≫
            (comonadPow G n).map (L.functor.map f)) := by
        rw [← R.functor.map_comp]
      _ = R.functor.map ((comonadPow G (n + 1)).map (L.functor.map f) ≫
            cobarEpsilonAtPos G n i (L.functor.obj b)) := by
        rw [hε]
      _ = R.functor.map ((comonadPow G (n + 1)).map (L.functor.map f)) ≫
            R.functor.map (cobarEpsilonAtPos G n i (L.functor.obj b)) := by
        rw [R.functor.map_comp]

/-- The component formula for a two-sided cobar codegeneracy.

At `a`, codegeneracy `i` is `R.map(cobarEpsilonAtPos G n i (L(a)))`. -/
@[simp] lemma cobarCodegeneracy_app (n : ℕ) (i : Fin (n + 1)) (a : A) :
    (cobarCodegeneracy n i).app a =
      R.functor.map (cobarEpsilonAtPos G n i (L.functor.obj a)) := rfl

end Elementary

end Comonad

end CategoryTheory
