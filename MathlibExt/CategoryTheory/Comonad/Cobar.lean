/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Comonad.Comodule

/-!
# Two-sided comonadic cobar construction – levelwise core + elementary operators

Mathematical source: J. P. May, *The Geometry of Iterated Loop Spaces*,
Lecture Notes in Mathematics 271, Springer, 1972, Chapter 9,
Construction 9.6 and Remark 9.12, <https://doi.org/10.1007/BFb0067491>.

This file is the formal categorical dual of that cited bar construction:
comonad `G` for monad `T`, comultiplication `δ` for multiplication `μ`,
counit `ε` for unit `η`, and endpoint coactions for endpoint actions.
Dual companion of the monadic bar core (`Monad.Bar`): for a comonad `G` on `C`
with a right comodule `R : C ⥤ D` and a left comodule `L : A ⥤ C`, the
degree-`n` cobar functor is `R.obj ((comonadPow G n).obj (L.obj a))`, i.e.
`R (G^n (L a))`.

General machinery: `comonadPow`, `comonadPow_obj_G_comm`,
`comonadPow_succ_obj_eq`, `deltaAtPos`, `epsilonAtPos` with naturality, public
reversed wrappers `cobarDeltaAtPos n i = deltaAtPos n i.rev` and
`cobarEpsilonAtPos n i = epsilonAtPos n i.rev` with naturality, reusable
recursive iterated right-comodule coaction `rightCoactionPow` with naturality,
`cobarObj` with `cobarObj_obj`, `cobarObj_map`, `cobarObj_zero`,
`cobarCofaceApp` component formula, `cobarCoface n i : C_n ⟶ C_{n+1}`
(`δ⁰` recursive iterated right coaction, `δ^{n+1}` left coaction, interior
`cobarDeltaAtPos`), `cobarCodegeneracy n i : C_{n+1} ⟶ C_n` via
`cobarEpsilonAtPos`.

Public indexing convention (counted from the right-comodule end, dual to the
bar convention `d₀ =` right action):
- `δ⁰ a = rightCoactionPow G R n (L a)` with
  `rightCoactionPow G R 0 X = R.coaction.app X` definitionally and
  `rightCoactionPow G R (n+1) X`
  `= rightCoactionPow G R n (G.toFunctor.obj X)` definitionally;
- `δ^{n+1} a = R.map (G^n.map (L.coaction.app a))`;
- `δ^{i+1} a = R.map (cobarDeltaAtPos G n i (L a))` for `i : Fin n`;
- `σ^i a = R.map (cobarEpsilonAtPos G n i (L a))` for `i : Fin (n+1)`.

The raw helpers `deltaAtPos`/`epsilonAtPos` count insertion positions from the
left-comodule end; the public wrappers reverse with `Fin.rev`, so `δ¹` uses the
raw last position and `δ^n` the raw position zero. The recursive
`rightCoactionPow` keeps the left-associated `comonadPow` while giving
transport-free equations for the right endpoint; the left endpoint is already
definitional.

All operators are defined directly and proved by induction mirroring the bar
calculus, keeping every component formula definitional, with public formulas
and no opposite-monad transport dependency or equivalence claimed.


-/

@[expose] public section

namespace CategoryTheory
namespace Comonad

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {A : Type u₃} [Category.{v₃} A]

/-- Iterated comonad powers, left-associated: `G^(n+1) = G ⋙ G^n`. -/
abbrev comonadPow (G : Comonad C) : ℕ → C ⥤ C
| 0 => 𝟭 C
| n + 1 => (G : C ⥤ C) ⋙ comonadPow G n

/-- Degree-zero power is the identity functor. -/
@[simp] lemma comonadPow_zero (G : Comonad C) : comonadPow G 0 = 𝟭 C := rfl

/-- Successor power unfolds one left-associated copy of `G`. -/
@[simp] lemma comonadPow_succ (G : Comonad C) (n : ℕ) :
    comonadPow G (n + 1) = (G : C ⥤ C) ⋙ comonadPow G n := rfl

/-- Powers commute with application of `G` on objects. -/
theorem comonadPow_obj_G_comm (G : Comonad C) (n : ℕ) (X : C) :
    (comonadPow G n).obj (G.toFunctor.obj X) =
      G.toFunctor.obj ((comonadPow G n).obj X) := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih => exact ih (G.toFunctor.obj X)

/-- Successor power applied to an object. -/
theorem comonadPow_succ_obj_eq (G : Comonad C) (n : ℕ) (X : C) :
    (comonadPow G (n + 1)).obj X = G.toFunctor.obj ((comonadPow G n).obj X) :=
  comonadPow_obj_G_comm G n X

/-- Comultiplication insertion at an arbitrary raw position:
`(G^n).obj X ⟶ (G^{n+1}).obj X`. Position zero applies `G.δ` under `G^n`;
later positions recurse under `G`. Counts from the left-comodule end. -/
noncomputable def deltaAtPos (G : Comonad C) : (n : ℕ) → (i : Fin n) → (X : C) →
    (comonadPow G n).obj X ⟶ (comonadPow G (n + 1)).obj X
| 0, i, _ => nomatch i
| n + 1, ⟨0, _⟩, X => (comonadPow G n).map (G.δ.app X)
| n + 1, ⟨k + 1, hk⟩, X => deltaAtPos G n ⟨k, by omega⟩ (G.toFunctor.obj X)

/-- Naturality of comultiplication insertion in the carrier object. -/
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

/-- Counit insertion at an arbitrary raw position:
`(G^{n+1}).obj X ⟶ (G^n).obj X`. The base case is `G.ε`; position zero maps
`G.ε` under `G^{n+1}`; later positions recurse under `G`. Counts from the
left-comodule end. -/
noncomputable def epsilonAtPos (G : Comonad C) : (n : ℕ) → (i : Fin (n + 1)) →
    (X : C) → (comonadPow G (n + 1)).obj X ⟶ (comonadPow G n).obj X
| 0, _, X => G.ε.app X
| n + 1, ⟨0, _⟩, X => (comonadPow G (n + 1)).map (G.ε.app X)
| n + 1, ⟨k + 1, hk⟩, X => epsilonAtPos G n ⟨k, by omega⟩ (G.toFunctor.obj X)

/-- Naturality of counit insertion in the carrier object. -/
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

/-- Public reversed-position wrapper for interior cobar cofaces: counts from the
right-comodule end (`δ⁰` = right coaction), i.e.
`cobarDeltaAtPos n i = deltaAtPos n i.rev`. Raw `deltaAtPos` is preserved
unchanged and counts from the left-comodule end. -/
noncomputable def cobarDeltaAtPos (G : Comonad C) (n : ℕ) (i : Fin n) (X : C) :
    (comonadPow G n).obj X ⟶ (comonadPow G (n + 1)).obj X :=
  deltaAtPos G n i.rev X

/-- Public reversed-position wrapper for cobar codegeneracies:
`cobarEpsilonAtPos n i = epsilonAtPos n i.rev`. -/
noncomputable def cobarEpsilonAtPos (G : Comonad C) (n : ℕ) (i : Fin (n + 1))
    (X : C) :
    (comonadPow G (n + 1)).obj X ⟶ (comonadPow G n).obj X :=
  epsilonAtPos G n i.rev X

/-- The reversed wrapper unfolds to the raw operator at `i.rev`. -/
@[simp] lemma cobarDeltaAtPos_rev (G : Comonad C) (n : ℕ) (i : Fin n) (X : C) :
    cobarDeltaAtPos G n i X = deltaAtPos G n i.rev X := rfl

/-- The reversed wrapper unfolds to the raw operator at `i.rev`. -/
@[simp] lemma cobarEpsilonAtPos_rev (G : Comonad C) (n : ℕ) (i : Fin (n + 1))
    (X : C) :
    cobarEpsilonAtPos G n i X = epsilonAtPos G n i.rev X := rfl

/-- Naturality of the public interior-coface insertion. -/
lemma cobarDeltaAtPos_naturality (G : Comonad C) (n : ℕ) (i : Fin n) {X Y : C}
    (f : X ⟶ Y) :
    (comonadPow G n).map f ≫ cobarDeltaAtPos G n i Y =
    cobarDeltaAtPos G n i X ≫ (comonadPow G (n + 1)).map f := by
  simp only [cobarDeltaAtPos]
  exact deltaAtPos_naturality G n i.rev f

/-- Naturality of the public codegeneracy insertion. -/
lemma cobarEpsilonAtPos_naturality (G : Comonad C) (n : ℕ) (i : Fin (n + 1))
    {X Y : C} (f : X ⟶ Y) :
    (comonadPow G (n + 1)).map f ≫ cobarEpsilonAtPos G n i Y =
    cobarEpsilonAtPos G n i X ≫ (comonadPow G n).map f := by
  simp only [cobarEpsilonAtPos]
  exact epsilonAtPos_naturality G n i.rev f

section Elementary

variable {G : Comonad C} {R : RightComodule G D} {L : LeftComodule A G}

/-- Degree-`n` cobar functor `R (G^n (L -)) : A ⥤ D`. -/
abbrev cobarObj (G : Comonad C) (R : RightComodule G D) (L : LeftComodule A G)
    (n : ℕ) : A ⥤ D :=
  (L.functor ⋙ comonadPow G n) ⋙ R.functor

/-- Objects of the degree-`n` cobar functor. -/
@[simp] lemma cobarObj_obj (G : Comonad C) (R : RightComodule G D)
    (L : LeftComodule A G) (n : ℕ) (a : A) :
    (cobarObj G R L n).obj a =
      R.functor.obj ((comonadPow G n).obj (L.functor.obj a)) := rfl

/-- Morphisms of the degree-`n` cobar functor. -/
@[simp] lemma cobarObj_map {G : Comonad C} {R : RightComodule G D}
    {L : LeftComodule A G} {n : ℕ} {a b : A} (f : a ⟶ b) :
    (cobarObj G R L n).map f =
      R.functor.map ((comonadPow G n).map (L.functor.map f)) := rfl

/-- Degree zero is the composite of the two underlying functors. -/
@[simp] lemma cobarObj_zero (G : Comonad C) (R : RightComodule G D)
    (L : LeftComodule A G) :
    cobarObj G R L 0 = L.functor ⋙ R.functor := rfl

/-- Reusable recursive iterated right-comodule coaction:
`R.functor.obj ((comonadPow G n).obj X) ⟶ R.functor.obj ((comonadPow G (n+1)).obj X)`.
Degree zero is definitionally `R.coaction.app X`; successor is definitionally
the preceding iterated coaction evaluated at `G.toFunctor.obj X`. This gives
transport-free recursive equations for the right endpoint while keeping
left-associated `comonadPow`. -/
noncomputable def rightCoactionPow (G : Comonad C) (R : RightComodule G D) :
    (n : ℕ) → (X : C) → R.functor.obj ((comonadPow G n).obj X) ⟶
      R.functor.obj ((comonadPow G (n + 1)).obj X)
| 0, X => R.coaction.app X
| n + 1, X => rightCoactionPow G R n (G.toFunctor.obj X)

/-- Degree zero is the comodule coaction. -/
@[simp] lemma rightCoactionPow_zero (G : Comonad C) (R : RightComodule G D)
    (X : C) :
    rightCoactionPow G R 0 X = R.coaction.app X := rfl

/-- Successor is the preceding iterated coaction under `G`. -/
@[simp] lemma rightCoactionPow_succ (G : Comonad C) (R : RightComodule G D)
    (n : ℕ) (X : C) :
    rightCoactionPow G R (n + 1) X =
      rightCoactionPow G R n (G.toFunctor.obj X) := rfl

/-- Naturality of the iterated right coaction in the carrier object. -/
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

/-- Component formula for cofaces: extracted to avoid self-reference while
defining `cobarCoface`. The right endpoint `δ⁰` is the reusable recursive
iterated right coaction `rightCoactionPow G R n (L a)`. The left endpoint
`δ^{n+1}` is the left coaction. Interior cofaces use the public
reversed-position wrapper `cobarDeltaAtPos`, i.e. `deltaAtPos` with `Fin.rev`. -/
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

/-- Cofaces assemble into natural transformations `C_n ⟶ C_{n+1}`. -/
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

/-- The zeroth coface is the iterated right coaction. -/
@[simp] lemma cobarCofaceApp_right (n : ℕ) (a : A) :
    cobarCofaceApp n ⟨0, by omega⟩ a =
      rightCoactionPow G R n (L.functor.obj a) := rfl

/-- The zeroth coface is the iterated right coaction. -/
@[simp] lemma cobarCoface_right (n : ℕ) (a : A) :
    (cobarCoface n ⟨0, by omega⟩).app a =
      rightCoactionPow G R n (L.functor.obj a) := rfl

/-- The last coface is the left coaction. -/
@[simp] lemma cobarCofaceApp_left (n : ℕ) (a : A) :
    cobarCofaceApp n ⟨n + 1, by omega⟩ a =
      R.functor.map ((comonadPow G n).map (L.coaction.app a)) := by
  have h0 : ¬ ((⟨n + 1, by omega⟩ : Fin (n + 2)).val = 0) := by simp
  have hlast : ((⟨n + 1, by omega⟩ : Fin (n + 2)).val = n + 1) := rfl
  unfold cobarCofaceApp
  rw [dite_eq_right h0, dite_eq_left hlast]

/-- The last coface is the left coaction. -/
@[simp] lemma cobarCoface_left (n : ℕ) (a : A) :
    (cobarCoface n ⟨n + 1, by omega⟩).app a =
      R.functor.map ((comonadPow G n).map (L.coaction.app a)) := by
  change cobarCofaceApp n ⟨n + 1, by omega⟩ a = _
  rw [cobarCofaceApp_left]

/-- Interior cofaces insert comultiplication at the reversed position. -/
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

/-- Interior cofaces insert comultiplication at the reversed position. -/
@[simp] lemma cobarCoface_middle (n : ℕ) (i : Fin n) (a : A) :
    (cobarCoface n ⟨i.val + 1,
        Nat.lt_trans (Nat.succ_lt_succ i.isLt) (Nat.lt_succ_self _)⟩).app a =
      R.functor.map (cobarDeltaAtPos G n i (L.functor.obj a)) := by
  simp only [cobarCoface, cobarCofaceApp_middle]

/-- Codegeneracies assemble into natural transformations `C_{n+1} ⟶ C_n`
via counit insertion. -/
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

/-- Components of codegeneracies are counit insertions mapped by `R`. -/
@[simp] lemma cobarCodegeneracy_app (n : ℕ) (i : Fin (n + 1)) (a : A) :
    (cobarCodegeneracy n i).app a =
      R.functor.map (cobarEpsilonAtPos G n i (L.functor.obj a)) := rfl

end Elementary

end Comonad

end CategoryTheory
