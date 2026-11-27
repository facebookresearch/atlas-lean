/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Monad.Module

/-!
# Two-sided monadic bar construction – levelwise core + elementary operators

Mathematical source: J. P. May, *The Geometry of Iterated Loop Spaces*,
Lecture Notes in Mathematics 271, Springer, 1972, Chapter 9,
Construction 9.6 and Remark 9.12, <https://doi.org/10.1007/BFb0067491>.

May's functor-valued two-sided bar has degree `n` of the form `Y C^n X`;
here `B(R,T,L)_n = R(T^n(L(-)))`, written in Lean's diagrammatic functor
order as `L.functor ⋙ monadPow T n ⋙ R.functor`. This API publicly counts
faces from the right-module end (`d₀` is the right action and `d_{n+1}`
the left action), while the internal `muAtPos`/`etaAtPos` count from the
left-module end and `barMuAtPos`/`barEtaAtPos` apply `Fin.rev`.

General machinery: `monadPow`, `monadPow_obj_T_comm`, `monadPow_succ_obj_eq`,
naturality lemmas, `muAtPos`, `etaAtPos` with naturality, public reversed
wrappers `barMuAtPos n i = muAtPos n i.rev` and `barEtaAtPos n i = etaAtPos n i.rev`
with naturality, recursive iterated right-module action `rightActionPow`
with naturality and optional comparison to the old `eqToHom` formula, `barObj`
with `barObj_obj`, `barObj_map`, `barObj_zero`, `barFaceApp` component formula,
`barFace n i : B_{n+1} ⟶ B_n` (`d₀` recursive iterated right action, `d_{n+1}`
left action, interior `barMuAtPos`), `barDegeneracy n i : B_n ⟶ B_{n+1}` via
`barEtaAtPos`.

Formulas (public convention `d₀ =` right action, `d_{n+1} =` left action):
- `d₀ a = rightActionPow T R n (L a)` with
  `rightActionPow T R 0 X = R.action X` definitionally and
  `rightActionPow T R (n+1) X = rightActionPow T R n (T X)` definitionally;
  equals `R.map (eqToHom (T^{n+1}(L a) = T(T^n(L a)))) ≫ R.action (T^n(L a))`
  via `rightActionPow_eq`
- `d_{n+1} a = R.map (T^n.map (L.action a))`
- `d_{i+1} a = R.map (barMuAtPos n i (L a))` for `i:Fin n`
- `s_i a = R.map (barEtaAtPos n i (L a))`

Algebra-valued evaluation `B(R,T,A)` via algebra objects is deferred to the
first specialization.

Deferred: arbitrary `φ`, simplicial identities, `SimplicialObject`,
augmentations, extra degeneracies.
-/

@[expose] public section

namespace CategoryTheory
namespace Monad

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {A : Type u₃} [Category.{v₃} A]

/--
Left-associated monad power `T ^ n`: `T ^ 0 = 𝟭` and
`T ^ (n + 1) = T ⋙ T ^ n`. Bar degree `n` is `R ∘ T ^ n ∘ L`.
-/
abbrev monadPow (T : Monad C) : ℕ → C ⥤ C
| 0 => 𝟭 C
| n + 1 => (T : C ⥤ C) ⋙ monadPow T n

@[simp] lemma monadPow_zero (T : Monad C) : monadPow T 0 = 𝟭 C := rfl
@[simp] lemma monadPow_succ (T : Monad C) (n : ℕ) :
    monadPow T (n + 1) = (T : C ⥤ C) ⋙ monadPow T n := rfl

set_option linter.defProp false in
def monadPow_obj_T_comm (T : Monad C) : (n : ℕ) → (X : C) →
    (monadPow T n).obj (T.obj X) = T.obj ((monadPow T n).obj X)
| 0, _ => rfl
| n + 1, X => monadPow_obj_T_comm T n (T.obj X)

set_option linter.defProp false in
def monadPow_succ_obj_eq (T : Monad C) (n : ℕ) (X : C) :
    (monadPow T (n + 1)).obj X = T.obj ((monadPow T n).obj X) :=
  monadPow_obj_T_comm T n X

lemma monadPow_obj_T_comm_naturality (T : Monad C) (n : ℕ) {X Y : C} (f : X ⟶ Y) :
    (monadPow T n).map (T.map f) ≫ eqToHom (monadPow_obj_T_comm T n Y) =
    eqToHom (monadPow_obj_T_comm T n X) ≫ T.map ((monadPow T n).map f) := by
  induction n generalizing X Y with
  | zero => simp
  | succ n ih => exact ih (T.map f)

lemma monadPow_succ_obj_eq_naturality (T : Monad C) (n : ℕ) {X Y : C} (f : X ⟶ Y) :
    (monadPow T (n + 1)).map f ≫ eqToHom (monadPow_succ_obj_eq T n Y) =
    eqToHom (monadPow_succ_obj_eq T n X) ≫ T.map ((monadPow T n).map f) :=
  monadPow_obj_T_comm_naturality T n f

/--
Raw left-counted multiplication `T ^ (n + 1) ⟶ T ^ n`: position `0` is the
innermost (left-module end) factor and successors recurse under `T`. Public bar
faces use the right-counted wrapper `barMuAtPos n i = muAtPos n i.rev`.
-/
noncomputable def muAtPos (T : Monad C) : (n : ℕ) → (i : Fin n) → (X : C) →
    (monadPow T (n + 1)).obj X ⟶ (monadPow T n).obj X
| 0, i, _ => nomatch i
| n + 1, ⟨0, _⟩, X => (monadPow T n).map (T.μ.app X)
| n + 1, ⟨k + 1, hk⟩, X => muAtPos T n ⟨k, by omega⟩ (T.obj X)

lemma muAtPos_naturality (T : Monad C) (n : ℕ) (k : Fin n) {X Y : C} (f : X ⟶ Y) :
    (monadPow T (n + 1)).map f ≫ muAtPos T n k Y =
    muAtPos T n k X ≫ (monadPow T n).map f := by
  induction n generalizing X Y with
  | zero => exact isEmptyElim k
  | succ n ih =>
    match k with
    | ⟨0, _⟩ =>
      have h1 : (monadPow T (n + 1 + 1)).map f = (monadPow T n).map (T.map (T.map f)) := rfl
      have h2 : (monadPow T (n + 1)).map f = (monadPow T n).map (T.map f) := rfl
      simp only [muAtPos] at *
      rw [h1, h2]
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      exact T.μ.naturality f
    | ⟨k + 1, hk⟩ =>
      simp only [muAtPos]
      exact ih ⟨k, by omega⟩ (T.map f)

/--
Raw left-counted unit insertion `T ^ n ⟶ T ^ (n + 1)`: position `0` is the
innermost (left-module end) factor and successors recurse under `T`. Public bar
degeneracies use the right-counted wrapper `barEtaAtPos n i = etaAtPos n i.rev`.
-/
noncomputable def etaAtPos (T : Monad C) : (n : ℕ) → (i : Fin (n + 1)) → (X : C) →
    (monadPow T n).obj X ⟶ (monadPow T (n + 1)).obj X
| 0, _, X => T.η.app X
| n + 1, ⟨0, _⟩, X => (monadPow T (n + 1)).map (T.η.app X)
| n + 1, ⟨k + 1, hk⟩, X => etaAtPos T n ⟨k, by omega⟩ (T.obj X)

lemma etaAtPos_naturality (T : Monad C) (n : ℕ) (i : Fin (n + 1)) {X Y : C} (f : X ⟶ Y) :
    (monadPow T n).map f ≫ etaAtPos T n i Y =
    etaAtPos T n i X ≫ (monadPow T (n + 1)).map f := by
  induction n generalizing X Y with
  | zero => simp only [etaAtPos]; exact T.η.naturality f
  | succ n ih =>
    match i with
    | ⟨0, _⟩ =>
      have hη : f ≫ T.η.app Y = T.η.app X ≫ T.map f := T.η.naturality f
      calc
        (monadPow T (n + 1)).map f ≫ (monadPow T (n + 1)).map (T.η.app Y)
            = (monadPow T n).map (T.map f) ≫ (monadPow T n).map (T.map (T.η.app Y)) := rfl
        _ = (monadPow T n).map (T.map f ≫ T.map (T.η.app Y)) := by rw [← Functor.map_comp]
        _ = (monadPow T n).map (T.map (f ≫ T.η.app Y)) := by rw [← Functor.map_comp]
        _ = (monadPow T n).map (T.map (T.η.app X ≫ T.map f)) := by rw [hη]
        _ = (monadPow T n).map (T.map (T.η.app X) ≫ T.map (T.map f)) := by rw [Functor.map_comp]
        _ = (monadPow T n).map (T.map (T.η.app X)) ≫ (monadPow T n).map (T.map (T.map f)) := by
              rw [Functor.map_comp]
        _ = (monadPow T (n + 1)).map (T.η.app X) ≫ (monadPow T (n + 1 + 1)).map f := rfl
    | ⟨k + 1, hk⟩ =>
      simp only [etaAtPos]
      exact ih ⟨k, by omega⟩ (T.map f)

/--
Public reversed-position wrapper for inner bar faces: counts from the right-module end
(`d₀` = right action), i.e. `barMuAtPos n i = muAtPos n i.rev`. Raw `muAtPos` is preserved
unchanged and counts from the left-module end.
-/
noncomputable def barMuAtPos (T : Monad C) (n : ℕ) (i : Fin n) (X : C) :
    (monadPow T (n + 1)).obj X ⟶ (monadPow T n).obj X :=
  muAtPos T n i.rev X

/-- Public reversed-position wrapper for bar degeneracies: `barEtaAtPos n i = etaAtPos n i.rev`. -/
noncomputable def barEtaAtPos (T : Monad C) (n : ℕ) (i : Fin (n + 1)) (X : C) :
    (monadPow T n).obj X ⟶ (monadPow T (n + 1)).obj X :=
  etaAtPos T n i.rev X

@[simp] lemma barMuAtPos_rev (T : Monad C) (n : ℕ) (i : Fin n) (X : C) :
    barMuAtPos T n i X = muAtPos T n i.rev X := rfl

@[simp] lemma barEtaAtPos_rev (T : Monad C) (n : ℕ) (i : Fin (n + 1)) (X : C) :
    barEtaAtPos T n i X = etaAtPos T n i.rev X := rfl

lemma barMuAtPos_naturality (T : Monad C) (n : ℕ) (i : Fin n) {X Y : C} (f : X ⟶ Y) :
    (monadPow T (n + 1)).map f ≫ barMuAtPos T n i Y =
    barMuAtPos T n i X ≫ (monadPow T n).map f := by
  simp only [barMuAtPos]
  exact muAtPos_naturality T n i.rev f

lemma barEtaAtPos_naturality (T : Monad C) (n : ℕ) (i : Fin (n + 1)) {X Y : C} (f : X ⟶ Y) :
    (monadPow T n).map f ≫ barEtaAtPos T n i Y =
    barEtaAtPos T n i X ≫ (monadPow T (n + 1)).map f := by
  simp only [barEtaAtPos]
  exact etaAtPos_naturality T n i.rev f

/-- Degree `n` object of the two-sided bar: `B(R,T,L)_n = L ⋙ T^n ⋙ R`. -/
abbrev barObj (T : Monad C) (R : RightModule T D) (L : LeftModule A T) (n : ℕ) : A ⥤ D :=
  (L.functor ⋙ monadPow T n) ⋙ R.functor

@[simp] lemma barObj_obj (T : Monad C) (R : RightModule T D) (L : LeftModule A T)
    (n : ℕ) (a : A) :
    (barObj T R L n).obj a = R.functor.obj ((monadPow T n).obj (L.functor.obj a)) := rfl

@[simp] lemma barObj_map {T : Monad C} {R : RightModule T D} {L : LeftModule A T}
    {n : ℕ} {a b : A} (f : a ⟶ b) :
    (barObj T R L n).map f = R.functor.map ((monadPow T n).map (L.functor.map f)) := rfl

@[simp] lemma barObj_zero (T : Monad C) (R : RightModule T D) (L : LeftModule A T) :
    barObj T R L 0 = L.functor ⋙ R.functor := rfl

set_option linter.defProp false in
/--
Recursive iterated right-module action:
`R.functor.obj ((monadPow T (n+1)).obj X) ⟶ R.functor.obj ((monadPow T n).obj X)`.
Degree zero is definitionally `R.action.app X`; successor is definitionally the preceding
iterated action evaluated at `T.obj X`. This avoids `eqToHom` transports for the right
endpoint while keeping left-associated `monadPow` and all pure `mu`/`eta` coherence.
-/
noncomputable def rightActionPow (T : Monad C) (R : RightModule T D) :
    (n : ℕ) → (X : C) → R.functor.obj ((monadPow T (n + 1)).obj X) ⟶
      R.functor.obj ((monadPow T n).obj X)
| 0, X => R.action.app X
| n + 1, X => rightActionPow T R n (T.obj X)

@[simp] lemma rightActionPow_zero (T : Monad C) (R : RightModule T D) (X : C) :
    rightActionPow T R 0 X = R.action.app X := rfl

@[simp] lemma rightActionPow_succ (T : Monad C) (R : RightModule T D) (n : ℕ) (X : C) :
    rightActionPow T R (n + 1) X = rightActionPow T R n (T.obj X) := rfl

lemma rightActionPow_naturality (T : Monad C) (R : RightModule T D) (n : ℕ) {X Y : C} (f : X ⟶ Y) :
    R.functor.map ((monadPow T (n + 1)).map f) ≫ rightActionPow T R n Y =
    rightActionPow T R n X ≫ R.functor.map ((monadPow T n).map f) := by
  induction n generalizing X Y with
  | zero =>
    simp only [rightActionPow]
    exact R.action.naturality f
  | succ n ih =>
    simp only [rightActionPow]
    exact ih (X := T.obj X) (Y := T.obj Y) (f := T.map f)

theorem rightActionPow_eq (T : Monad C) (R : RightModule T D) (n : ℕ) (X : C) :
    rightActionPow T R n X =
      R.functor.map (eqToHom (monadPow_succ_obj_eq T n X)) ≫
        R.action.app ((monadPow T n).obj X) := by
  induction n generalizing X with
  | zero =>
    have hMap : R.functor.map (eqToHom (monadPow_succ_obj_eq T 0 X)) = 𝟙 _ := by
      simp
    have h : R.functor.map (eqToHom (monadPow_succ_obj_eq T 0 X)) ≫
        R.action.app ((monadPow T 0).obj X) =
        R.action.app ((monadPow T 0).obj X) := by
      rw [hMap, Category.id_comp]
    calc
      rightActionPow T R 0 X = R.action.app X := rfl
      _ = R.action.app ((monadPow T 0).obj X) := rfl
      _ = R.functor.map (eqToHom (monadPow_succ_obj_eq T 0 X)) ≫
            R.action.app ((monadPow T 0).obj X) := h.symm
  | succ n ih =>
    calc
      rightActionPow T R (n + 1) X = rightActionPow T R n (T.obj X) := rfl
      _ = R.functor.map (eqToHom (monadPow_succ_obj_eq T n (T.obj X))) ≫
            R.action.app ((monadPow T n).obj (T.obj X)) := ih (T.obj X)
      _ = R.functor.map (eqToHom (monadPow_succ_obj_eq T (n + 1) X)) ≫
            R.action.app ((monadPow T (n + 1)).obj X) := by rfl

/--
Two successive iterated right actions equal the outermost/raw-last
multiplication `muAtPos (n+1) last` followed by `rightActionPow`. Proved by
induction via `rightActionPow_succ` and `muAtPos_succ_eq`; base case is the
right-module associativity.
-/
theorem rightActionPow_assoc_last (T : Monad C) (R : RightModule T D) (n : ℕ) (X : C) :
    rightActionPow T R (n + 1) X ≫ rightActionPow T R n X =
      R.functor.map (muAtPos T (n + 1) ⟨n, by omega⟩ X) ≫ rightActionPow T R n X := by
  induction n generalizing X with
  | zero =>
    simp only [rightActionPow]
    exact (RightModule.assoc_app R X).symm
  | succ n ih =>
    calc
      rightActionPow T R (n + 2) X ≫ rightActionPow T R (n + 1) X
          = rightActionPow T R (n + 1) (T.obj X) ≫ rightActionPow T R n (T.obj X) := rfl
      _ = R.functor.map (muAtPos T (n + 1) ⟨n, by omega⟩ (T.obj X)) ≫
            rightActionPow T R n (T.obj X) := ih (T.obj X)
      _ = R.functor.map (muAtPos T (n + 2) ⟨n + 1, by omega⟩ X) ≫
            rightActionPow T R (n + 1) X := by
        have hmu : muAtPos T (n + 2) ⟨n + 1, by omega⟩ X =
            muAtPos T (n + 1) ⟨n, by omega⟩ (T.obj X) := rfl
        rw [hmu]
        rfl

/--
Raw-last unit insertion followed by the iterated right action is the
identity. Proved by induction via `rightActionPow_succ` and
`etaAtPos_succ_eq`; base case is the right-module unit.
-/
theorem rightActionPow_unit_last (T : Monad C) (R : RightModule T D) (n : ℕ) (X : C) :
    R.functor.map (etaAtPos T n ⟨n, by omega⟩ X) ≫ rightActionPow T R n X = 𝟙 _ := by
  induction n generalizing X with
  | zero =>
    simp only [etaAtPos, rightActionPow]
    exact RightModule.unit_app R X
  | succ n ih =>
    calc
      R.functor.map (etaAtPos T (n + 1) ⟨n + 1, by omega⟩ X) ≫
            rightActionPow T R (n + 1) X
          = R.functor.map (etaAtPos T n ⟨n, by omega⟩ (T.obj X)) ≫
              rightActionPow T R n (T.obj X) := rfl
      _ = 𝟙 _ := ih (T.obj X)

/--
Distant right-endpoint interchange:
`muAtPos` at degree `n+1` and position `castSucc i` commutes with `rightActionPow`.
For `n`, `i : Fin n`, `R.map (muAtPos (n+1) (castSucc i)) ≫ rightActionPow n =
rightActionPow (n+1) ≫ R.map (muAtPos n i)`.
Proved by induction on `n`, using definitional successor equations (`rightActionPow_succ`,
`muAtPos_succ_eq`) with explicit `change` where elaboration does not unfold, and
`rightActionPow_naturality` for the raw position-zero case.
-/
theorem rightActionPow_mu_castSucc (T : Monad C) (R : RightModule T D) (n : ℕ)
    (i : Fin n) (X : C) :
    R.functor.map (muAtPos T (n + 1) i.castSucc X) ≫ rightActionPow T R n X =
    rightActionPow T R (n + 1) X ≫ R.functor.map (muAtPos T n i X) := by
  induction n generalizing X with
  | zero =>
    exact isEmptyElim i
  | succ n ih =>
    match i with
    | ⟨0, hi⟩ =>
      have hcast0 : (Fin.castSucc (⟨0, hi⟩ : Fin (n + 1)) : Fin (n + 2)) = ⟨0, by omega⟩ := by
        apply Fin.ext; simp
      -- explicit change for the castSucc position, elaboration does not unfold it automatically
      change R.functor.map (muAtPos T (n + 2) (Fin.castSucc (⟨0, hi⟩ : Fin (n + 1))) X) ≫
          rightActionPow T R (n + 1) X =
        rightActionPow T R (n + 2) X ≫
          R.functor.map (muAtPos T (n + 1) (⟨0, hi⟩ : Fin (n + 1)) X)
      rw [hcast0]
      -- make definitional rightActionPow successor explicit
      change R.functor.map ((monadPow T (n + 1)).map (T.μ.app X)) ≫
          rightActionPow T R (n + 1) X =
        rightActionPow T R (n + 2) X ≫
          R.functor.map ((monadPow T n).map (T.μ.app X))
      have hr1 : rightActionPow T R (n + 1) X = rightActionPow T R n (T.obj X) := rfl
      have hr2 : rightActionPow T R (n + 2) X = rightActionPow T R (n + 1) (T.obj X) := rfl
      rw [hr1, hr2]
      -- unfold once more for the raw zero naturality; use the functor-comp object form that
      -- appears in T.μ.app X's domain to match naturality's binder
      change R.functor.map ((monadPow T (n + 1)).map (T.μ.app X)) ≫
          rightActionPow T R n (T.obj X) =
        rightActionPow T R n ((T.toFunctor ⋙ T.toFunctor).obj X) ≫
          R.functor.map ((monadPow T n).map (T.μ.app X))
      -- raw position-zero case via rightActionPow_naturality
      exact rightActionPow_naturality T R n (f := T.μ.app X)
    | ⟨k + 1, hk⟩ =>
      let i0 : Fin n := ⟨k, by omega⟩
      have hcast_succ : (Fin.castSucc (⟨k + 1, hk⟩ : Fin (n + 1)) : Fin (n + 2)) =
          (Fin.castSucc i0).succ := by
        apply Fin.ext; simp [i0]
      have hmu_cast : muAtPos T (n + 2) (Fin.castSucc (⟨k + 1, hk⟩ : Fin (n + 1))) X =
          muAtPos T (n + 1) (Fin.castSucc i0) (T.obj X) := by
        rw [hcast_succ]; rfl
      have hmu_i : muAtPos T (n + 1) (⟨k + 1, hk⟩ : Fin (n + 1)) X =
          muAtPos T n i0 (T.obj X) := rfl
      have hr1 : rightActionPow T R (n + 1) X = rightActionPow T R n (T.obj X) := rfl
      have hr2 : rightActionPow T R (n + 2) X = rightActionPow T R (n + 1) (T.obj X) := rfl
      -- explicit change where elaboration keeps the raw succ equations folded
      change R.functor.map (muAtPos T (n + 2) (Fin.castSucc (⟨k + 1, hk⟩ : Fin (n + 1))) X) ≫
          rightActionPow T R (n + 1) X =
        rightActionPow T R (n + 2) X ≫
          R.functor.map (muAtPos T (n + 1) (⟨k + 1, hk⟩ : Fin (n + 1)) X)
      rw [hmu_cast, hmu_i, hr1, hr2]
      have h_eq : R.functor.map (muAtPos T (n + 1) (Fin.castSucc i0) (T.obj X)) ≫
          rightActionPow T R n (T.obj X) =
        rightActionPow T R (n + 1) (T.obj X) ≫
          R.functor.map (muAtPos T n i0 (T.obj X)) := ih i0 (T.obj X)
      change R.functor.map (muAtPos T (n + 1) (Fin.castSucc i0) (T.obj X)) ≫
          rightActionPow T R n (T.obj X) =
        rightActionPow T R n (T.obj (T.obj X)) ≫
          R.functor.map (muAtPos T n i0 (T.obj X))
      calc
        R.functor.map (muAtPos T (n + 1) (Fin.castSucc i0) (T.obj X)) ≫
              rightActionPow T R n (T.obj X)
            = rightActionPow T R (n + 1) (T.obj X) ≫
                R.functor.map (muAtPos T n i0 (T.obj X)) := h_eq
        _ = rightActionPow T R n (T.obj (T.obj X)) ≫
                R.functor.map (muAtPos T n i0 (T.obj X)) := rfl

/--
Distant right-endpoint unit insertion:
`etaAtPos` at degree `n+1` and position `castSucc i` commutes with `rightActionPow`.
For `n`, `i : Fin (n+1)`,
`R.map (etaAtPos (n+1) (castSucc i)) ≫ rightActionPow (n+1) = rightActionPow n ≫
R.map (etaAtPos n i)`.
Proved by induction on `n`, using definitional successor equations (`rightActionPow_succ`,
`etaAtPos_succ_eq`) with explicit `change` where elaboration does not unfold, and
`RightModule.action.naturality` in the base case and `rightActionPow_naturality` for the raw
position-zero case.
-/
theorem rightActionPow_eta_castSucc (T : Monad C) (R : RightModule T D) (n : ℕ)
    (i : Fin (n + 1)) (X : C) :
    R.functor.map (etaAtPos T (n + 1) i.castSucc X) ≫ rightActionPow T R (n + 1) X =
    rightActionPow T R n X ≫ R.functor.map (etaAtPos T n i X) := by
  induction n generalizing X with
  | zero =>
    have hi : i = ⟨0, by omega⟩ := by
      have : i.val = 0 := by omega
      ext; exact this
    subst hi
    change R.functor.map (etaAtPos T 1 (Fin.castSucc (⟨0, by omega⟩ : Fin 1)) X) ≫
        rightActionPow T R 1 X =
      rightActionPow T R 0 X ≫ R.functor.map (etaAtPos T 0 ⟨0, by omega⟩ X)
    have hcast : (Fin.castSucc (⟨0, by omega⟩ : Fin 1) : Fin 2) = ⟨0, by omega⟩ := by
      apply Fin.ext; simp
    rw [hcast]
    change R.functor.map ((monadPow T 1).map (T.η.app X)) ≫ rightActionPow T R 1 X =
      rightActionPow T R 0 X ≫ R.functor.map (T.η.app X)
    have hr1 : rightActionPow T R 0 X = R.action.app X := rfl
    have hr2 : rightActionPow T R 1 X = R.action.app (T.obj X) := rfl
    rw [hr1, hr2]
    change R.functor.map (T.map (T.η.app X)) ≫ R.action.app (T.obj X) =
      R.action.app X ≫ R.functor.map (T.η.app X)
    exact R.action.naturality (T.η.app X)
  | succ n ih =>
    match i with
    | ⟨0, hi⟩ =>
      have hcast0 : (Fin.castSucc (⟨0, hi⟩ : Fin (n + 2)) : Fin (n + 3)) = ⟨0, by omega⟩ := by
        apply Fin.ext; simp
      change R.functor.map (etaAtPos T (n + 2) (Fin.castSucc (⟨0, hi⟩ : Fin (n + 2))) X) ≫
          rightActionPow T R (n + 2) X =
        rightActionPow T R (n + 1) X ≫
          R.functor.map (etaAtPos T (n + 1) (⟨0, hi⟩ : Fin (n + 2)) X)
      rw [hcast0]
      change R.functor.map ((monadPow T (n + 2)).map (T.η.app X)) ≫
          rightActionPow T R (n + 2) X =
        rightActionPow T R (n + 1) X ≫
          R.functor.map ((monadPow T (n + 1)).map (T.η.app X))
      have hr1 : rightActionPow T R (n + 1) X = rightActionPow T R n (T.obj X) := rfl
      have hr2 : rightActionPow T R (n + 2) X = rightActionPow T R (n + 1) (T.obj X) := rfl
      rw [hr1, hr2]
      change R.functor.map ((monadPow T (n + 2)).map (T.η.app X)) ≫
          rightActionPow T R (n + 1) (T.obj X) =
        rightActionPow T R n (T.obj X) ≫
          R.functor.map ((monadPow T (n + 1)).map (T.η.app X))
      exact rightActionPow_naturality T R (n + 1) (f := T.η.app X)
    | ⟨k + 1, hk⟩ =>
      let i0 : Fin (n + 1) := ⟨k, by omega⟩
      have hcast_succ : (Fin.castSucc (⟨k + 1, hk⟩ : Fin (n + 2)) : Fin (n + 3)) =
          (Fin.castSucc i0).succ := by
        apply Fin.ext; simp [i0]
      have heta_cast : etaAtPos T (n + 2) (Fin.castSucc (⟨k + 1, hk⟩ : Fin (n + 2))) X =
          etaAtPos T (n + 1) (Fin.castSucc i0) (T.obj X) := by
        rw [hcast_succ]; rfl
      have heta_i : etaAtPos T (n + 1) (⟨k + 1, hk⟩ : Fin (n + 2)) X =
          etaAtPos T n i0 (T.obj X) := rfl
      have hr1 : rightActionPow T R (n + 1) X = rightActionPow T R n (T.obj X) := rfl
      have hr2 : rightActionPow T R (n + 2) X = rightActionPow T R (n + 1) (T.obj X) := rfl
      change R.functor.map (etaAtPos T (n + 2) (Fin.castSucc (⟨k + 1, hk⟩ : Fin (n + 2))) X) ≫
          rightActionPow T R (n + 2) X =
        rightActionPow T R (n + 1) X ≫
          R.functor.map (etaAtPos T (n + 1) (⟨k + 1, hk⟩ : Fin (n + 2)) X)
      rw [heta_cast, heta_i, hr1, hr2]
      have h_eq : R.functor.map (etaAtPos T (n + 1) (Fin.castSucc i0) (T.obj X)) ≫
          rightActionPow T R (n + 1) (T.obj X) =
        rightActionPow T R n (T.obj X) ≫
          R.functor.map (etaAtPos T n i0 (T.obj X)) := ih i0 (T.obj X)
      change R.functor.map (etaAtPos T (n + 1) (Fin.castSucc i0) (T.obj X)) ≫
          rightActionPow T R (n + 1) (T.obj X) =
        rightActionPow T R n (T.obj X) ≫
          R.functor.map (etaAtPos T n i0 (T.obj X))
      exact h_eq

/--
Raw-position-zero unit insertion at degree `n`, mapped by `R`,
followed by the left action whiskered by `monadPow n` and mapped by `R`,
is identity. Derived from `LeftModule.unit_app` and functoriality.
Parallel to `rightActionPow_unit_last`.
-/
theorem leftAction_unit_zero (T : Monad C) (R : RightModule T D) (L : LeftModule A T)
    (n : ℕ) (a : A) :
    R.functor.map (etaAtPos T n ⟨0, by omega⟩ (L.functor.obj a)) ≫
      R.functor.map ((monadPow T n).map (L.action.app a)) = 𝟙 _ := by
  have h_eta : etaAtPos T n ⟨0, by omega⟩ (L.functor.obj a) =
      (monadPow T n).map (T.η.app (L.functor.obj a)) := by
    cases n with
    | zero =>
      rfl
    | succ _ =>
      rfl
  calc
    R.functor.map (etaAtPos T n ⟨0, by omega⟩ (L.functor.obj a)) ≫
        R.functor.map ((monadPow T n).map (L.action.app a))
        = R.functor.map ((monadPow T n).map (T.η.app (L.functor.obj a))) ≫
          R.functor.map ((monadPow T n).map (L.action.app a)) := by
      rw [h_eta]
    _ = R.functor.map ((monadPow T n).map (T.η.app (L.functor.obj a)) ≫
          (monadPow T n).map (L.action.app a)) := by
      rw [← R.functor.map_comp]
    _ = R.functor.map ((monadPow T n).map (T.η.app (L.functor.obj a) ≫ L.action.app a)) := by
      rw [← (monadPow T n).map_comp]
    _ = R.functor.map ((monadPow T n).map (𝟙 (L.functor.obj a))) := by
      rw [LeftModule.unit_app L a]
    _ = R.functor.map (𝟙 ((monadPow T n).obj (L.functor.obj a))) := by
      rw [(monadPow T n).map_id]
    _ = 𝟙 _ := by
      rw [R.functor.map_id]

/--
Two successive left endpoint actions at degrees `n+1` and `n`
equal raw-position-zero multiplication at degree `n+1` followed by
the left endpoint action. Derived from `LeftModule.assoc_app` and functoriality.
Parallel to `rightActionPow_assoc_last`.
-/
theorem leftAction_assoc_zero (T : Monad C) (R : RightModule T D) (L : LeftModule A T)
    (n : ℕ) (a : A) :
    R.functor.map ((monadPow T (n + 1)).map (L.action.app a)) ≫
      R.functor.map ((monadPow T n).map (L.action.app a)) =
    R.functor.map (muAtPos T (n + 1) ⟨0, by omega⟩ (L.functor.obj a)) ≫
      R.functor.map ((monadPow T n).map (L.action.app a)) := by
  have h_pow_succ : (monadPow T (n + 1)).map (L.action.app a) =
      (monadPow T n).map (T.map (L.action.app a)) := rfl
  have h_mu_zero : muAtPos T (n + 1) ⟨0, by omega⟩ (L.functor.obj a) =
      (monadPow T n).map (T.μ.app (L.functor.obj a)) := rfl
  calc
    R.functor.map ((monadPow T (n + 1)).map (L.action.app a)) ≫
        R.functor.map ((monadPow T n).map (L.action.app a))
        = R.functor.map ((monadPow T n).map (T.map (L.action.app a))) ≫
          R.functor.map ((monadPow T n).map (L.action.app a)) := by
      rw [h_pow_succ]
    _ = R.functor.map ((monadPow T n).map (T.map (L.action.app a)) ≫
          (monadPow T n).map (L.action.app a)) := by
      rw [← R.functor.map_comp]
    _ = R.functor.map ((monadPow T n).map (T.map (L.action.app a) ≫ L.action.app a)) := by
      rw [← (monadPow T n).map_comp]
    _ = R.functor.map ((monadPow T n).map (T.μ.app (L.functor.obj a) ≫ L.action.app a)) := by
      rw [← LeftModule.assoc_app L a]
    _ = R.functor.map ((monadPow T n).map (T.μ.app (L.functor.obj a)) ≫
          (monadPow T n).map (L.action.app a)) := by
      rw [(monadPow T n).map_comp]
    _ = R.functor.map (muAtPos T (n + 1) ⟨0, by omega⟩ (L.functor.obj a) ≫
          (monadPow T n).map (L.action.app a)) := by
      rw [← h_mu_zero]
    _ = R.functor.map (muAtPos T (n + 1) ⟨0, by omega⟩ (L.functor.obj a)) ≫
          R.functor.map ((monadPow T n).map (L.action.app a)) := by
      rw [R.functor.map_comp]

/--
Right and left bar endpoints commute: mapping the left action through
`monadPow` at degree `n+1` and then applying `rightActionPow` at degree `n`
equals applying `rightActionPow` at degree `n+1` and then mapping the left
action through `monadPow` at degree `n`. Thin consequence of
`rightActionPow_naturality` at `L.action.app a` and the definitional
successor equation `rightActionPow_succ`.
-/
theorem rightActionPow_leftAction (T : Monad C) (R : RightModule T D)
    (L : LeftModule A T) (n : ℕ) (a : A) :
    R.functor.map ((monadPow T (n + 1)).map (L.action.app a)) ≫
      rightActionPow T R n (L.functor.obj a) =
    rightActionPow T R (n + 1) (L.functor.obj a) ≫
      R.functor.map ((monadPow T n).map (L.action.app a)) := by
  have h := rightActionPow_naturality T R n (f := L.action.app a)
  simpa using h

/--
Distant left-endpoint interchange for multiplication:
`muAtPos` at degree `n+1` and position `i.succ` commutes with the left action
mapped through `monadPow`. For `n`, `i : Fin n`, `a`,
`R.map (muAtPos (n+1) (i.succ)) ≫ R.map (monadPow n (L.action)) =
R.map (monadPow (n+1) (L.action)) ≫ R.map (muAtPos n i)`.
Thin consequence of `muAtPos_naturality` at `L.action.app a` and the definitional
successor equation for `muAtPos`, followed by `R.map`.
-/
theorem leftAction_mu_succ (T : Monad C) (R : RightModule T D) (L : LeftModule A T)
    (n : ℕ) (i : Fin n) (a : A) :
    R.functor.map (muAtPos T (n + 1) i.succ (L.functor.obj a)) ≫
      R.functor.map ((monadPow T n).map (L.action.app a)) =
    R.functor.map ((monadPow T (n + 1)).map (L.action.app a)) ≫
      R.functor.map (muAtPos T n i (L.functor.obj a)) := by
  have h_fin : (⟨i.val, by omega⟩ : Fin n) = i := by
    apply Fin.ext; rfl
  have hi_succ : i.succ = ⟨i.val + 1, by omega⟩ := by
    apply Fin.ext; simp
  have h_succ : muAtPos T (n + 1) i.succ (L.functor.obj a) =
      muAtPos T n i (T.obj (L.functor.obj a)) := by
    calc
      muAtPos T (n + 1) i.succ (L.functor.obj a)
          = muAtPos T (n + 1) ⟨i.val + 1, by omega⟩ (L.functor.obj a) := by rw [hi_succ]
      _ = muAtPos T n ⟨i.val, by omega⟩ (T.obj (L.functor.obj a)) := rfl
      _ = muAtPos T n i (T.obj (L.functor.obj a)) := by rw [h_fin]
  have h_nat := muAtPos_naturality (T := T) (n := n) (k := i) (f := L.action.app a)
  have h_raw : muAtPos T (n + 1) i.succ (L.functor.obj a) ≫
      (monadPow T n).map (L.action.app a) =
      (monadPow T (n + 1)).map (L.action.app a) ≫
        muAtPos T n i (L.functor.obj a) := by
    calc
      muAtPos T (n + 1) i.succ (L.functor.obj a) ≫
          (monadPow T n).map (L.action.app a)
          = muAtPos T n i (T.obj (L.functor.obj a)) ≫
            (monadPow T n).map (L.action.app a) := by rw [h_succ]
      _ = (monadPow T (n + 1)).map (L.action.app a) ≫
            muAtPos T n i (L.functor.obj a) := h_nat.symm
  calc
    R.functor.map (muAtPos T (n + 1) i.succ (L.functor.obj a)) ≫
        R.functor.map ((monadPow T n).map (L.action.app a))
        = R.functor.map (muAtPos T (n + 1) i.succ (L.functor.obj a) ≫
            (monadPow T n).map (L.action.app a)) := by
      rw [← R.functor.map_comp]
    _ = R.functor.map ((monadPow T (n + 1)).map (L.action.app a) ≫
            muAtPos T n i (L.functor.obj a)) := by rw [h_raw]
    _ = R.functor.map ((monadPow T (n + 1)).map (L.action.app a)) ≫
            R.functor.map (muAtPos T n i (L.functor.obj a)) := by
      rw [R.functor.map_comp]

/--
Distant left-endpoint interchange for unit insertion:
`etaAtPos` at degree `n+1` and position `i.succ` commutes with the left action
mapped through `monadPow`. For `n`, `i : Fin (n+1)`, `a`,
`R.map (etaAtPos (n+1) (i.succ)) ≫ R.map (monadPow (n+1) (L.action)) =
R.map (monadPow n (L.action)) ≫ R.map (etaAtPos n i)`.
Thin consequence of `etaAtPos_naturality` at `L.action.app a` and the definitional
successor equation for `etaAtPos`, followed by `R.map`.
-/
theorem leftAction_eta_succ (T : Monad C) (R : RightModule T D) (L : LeftModule A T)
    (n : ℕ) (i : Fin (n + 1)) (a : A) :
    R.functor.map (etaAtPos T (n + 1) i.succ (L.functor.obj a)) ≫
      R.functor.map ((monadPow T (n + 1)).map (L.action.app a)) =
    R.functor.map ((monadPow T n).map (L.action.app a)) ≫
      R.functor.map (etaAtPos T n i (L.functor.obj a)) := by
  have h_fin : (⟨i.val, by omega⟩ : Fin (n + 1)) = i := by
    apply Fin.ext; rfl
  have hi_succ : i.succ = ⟨i.val + 1, by omega⟩ := by
    apply Fin.ext; simp
  have h_succ : etaAtPos T (n + 1) i.succ (L.functor.obj a) =
      etaAtPos T n i (T.obj (L.functor.obj a)) := by
    calc
      etaAtPos T (n + 1) i.succ (L.functor.obj a)
          = etaAtPos T (n + 1) ⟨i.val + 1, by omega⟩ (L.functor.obj a) := by rw [hi_succ]
      _ = etaAtPos T n ⟨i.val, by omega⟩ (T.obj (L.functor.obj a)) := rfl
      _ = etaAtPos T n i (T.obj (L.functor.obj a)) := by rw [h_fin]
  have h_nat := etaAtPos_naturality (T := T) (n := n) (i := i) (f := L.action.app a)
  have h_raw : etaAtPos T (n + 1) i.succ (L.functor.obj a) ≫
      (monadPow T (n + 1)).map (L.action.app a) =
      (monadPow T n).map (L.action.app a) ≫
        etaAtPos T n i (L.functor.obj a) := by
    calc
      etaAtPos T (n + 1) i.succ (L.functor.obj a) ≫
          (monadPow T (n + 1)).map (L.action.app a)
          = etaAtPos T n i (T.obj (L.functor.obj a)) ≫
            (monadPow T (n + 1)).map (L.action.app a) := by rw [h_succ]
      _ = (monadPow T n).map (L.action.app a) ≫
            etaAtPos T n i (L.functor.obj a) := h_nat.symm
  calc
    R.functor.map (etaAtPos T (n + 1) i.succ (L.functor.obj a)) ≫
        R.functor.map ((monadPow T (n + 1)).map (L.action.app a))
        = R.functor.map (etaAtPos T (n + 1) i.succ (L.functor.obj a) ≫
            (monadPow T (n + 1)).map (L.action.app a)) := by
      rw [← R.functor.map_comp]
    _ = R.functor.map ((monadPow T n).map (L.action.app a) ≫
            etaAtPos T n i (L.functor.obj a)) := by rw [h_raw]
    _ = R.functor.map ((monadPow T n).map (L.action.app a)) ≫
            R.functor.map (etaAtPos T n i (L.functor.obj a)) := by
      rw [R.functor.map_comp]

section Elementary

variable {T : Monad C} {R : RightModule T D} {L : LeftModule A T}

/--
Component formula for faces: extracted to avoid self-reference while defining `barFace`.
The right endpoint `d₀` is the recursive iterated right action
`rightActionPow T R n (L a)`, avoiding `eqToHom` transports while keeping
left-associated `monadPow`. The left endpoint `d_{n+1}` is the left action.
Interior faces use the public reversed-position wrapper `barMuAtPos`, i.e.
`muAtPos` with `Fin.rev`.
-/
noncomputable def barFaceApp (n : ℕ) (i : Fin (n + 2)) (a : A) :
    (barObj T R L (n + 1)).obj a ⟶ (barObj T R L n).obj a :=
  if h0 : i.val = 0 then
    rightActionPow T R n (L.functor.obj a)
  else if hlast : i.val = n + 1 then
    R.functor.map ((monadPow T n).map (L.action.app a))
  else
    have hi : i.val < n + 2 := i.isLt
    have hk : i.val - 1 < n := by
      have h0' : 0 < i.val := by omega
      have hle : i.val ≤ n := by omega
      omega
    R.functor.map (barMuAtPos T n ⟨i.val - 1, hk⟩ (L.functor.obj a))

/--
Public face `d_i : B_{n+1} ⟶ B_n`: `d₀` is the right action,
  `d_{n+1}` is the left action, interior faces use `barMuAtPos`.
-/
noncomputable def barFace (n : ℕ) (i : Fin (n + 2)) :
    barObj T R L (n + 1) ⟶ barObj T R L n where
  app a := barFaceApp n i a
  naturality a b f := by
    have hF : (barObj T R L (n + 1)).map f =
        R.functor.map ((monadPow T (n + 1)).map (L.functor.map f)) := rfl
    have hG : (barObj T R L n).map f =
        R.functor.map ((monadPow T n).map (L.functor.map f)) := rfl
    by_cases h0 : i.val = 0
    · have ha : barFaceApp n i a = rightActionPow T R n (L.functor.obj a) := by
        unfold barFaceApp
        rw [dite_eq_left h0]
      have hb : barFaceApp n i b = rightActionPow T R n (L.functor.obj b) := by
        unfold barFaceApp
        rw [dite_eq_left h0]
      rw [ha, hb, hF, hG]
      exact rightActionPow_naturality T R n (L.functor.map f)
    · by_cases hlast : i.val = n + 1
      · have ha : barFaceApp n i a =
            R.functor.map ((monadPow T n).map (L.action.app a)) := by
          unfold barFaceApp
          rw [dite_eq_right h0, dite_eq_left hlast]
        have hb : barFaceApp n i b =
            R.functor.map ((monadPow T n).map (L.action.app b)) := by
          unfold barFaceApp
          rw [dite_eq_right h0, dite_eq_left hlast]
        rw [ha, hb, hF, hG]
        have hL : T.map (L.functor.map f) ≫ L.action.app b =
            L.action.app a ≫ L.functor.map f := by
          have := L.action.naturality f
          simpa using this
        have h1 : (monadPow T (n + 1)).map (L.functor.map f) =
            (monadPow T n).map (T.map (L.functor.map f)) := rfl
        calc
          R.functor.map ((monadPow T (n + 1)).map (L.functor.map f)) ≫
              R.functor.map ((monadPow T n).map (L.action.app b))
              = R.functor.map ((monadPow T n).map (T.map (L.functor.map f))) ≫
                  R.functor.map ((monadPow T n).map (L.action.app b)) := by rw [h1]
          _ = R.functor.map ((monadPow T n).map (T.map (L.functor.map f)) ≫
                  (monadPow T n).map (L.action.app b)) := by rw [← R.functor.map_comp]
          _ = R.functor.map ((monadPow T n).map (T.map (L.functor.map f) ≫ L.action.app b)) := by
                rw [← Functor.map_comp]
          _ = R.functor.map ((monadPow T n).map (L.action.app a ≫ L.functor.map f)) := by rw [hL]
          _ = R.functor.map ((monadPow T n).map (L.action.app a) ≫
                  (monadPow T n).map (L.functor.map f)) := by rw [Functor.map_comp]
          _ = R.functor.map ((monadPow T n).map (L.action.app a)) ≫
                  R.functor.map ((monadPow T n).map (L.functor.map f)) := by rw [R.functor.map_comp]
      · have hk : i.val - 1 < n := by omega
        let k : Fin n := ⟨i.val - 1, hk⟩
        have ha : barFaceApp n i a =
            R.functor.map (barMuAtPos T n k (L.functor.obj a)) := by
          unfold barFaceApp
          rw [dite_eq_right h0, dite_eq_right hlast]
        have hb : barFaceApp n i b =
            R.functor.map (barMuAtPos T n k (L.functor.obj b)) := by
          unfold barFaceApp
          rw [dite_eq_right h0, dite_eq_right hlast]
        rw [ha, hb, hF, hG]
        have hμ := barMuAtPos_naturality T n k (f := L.functor.map f)
        calc
          R.functor.map ((monadPow T (n + 1)).map (L.functor.map f)) ≫
              R.functor.map (barMuAtPos T n k (L.functor.obj b))
              = R.functor.map ((monadPow T (n + 1)).map (L.functor.map f) ≫
                  barMuAtPos T n k (L.functor.obj b)) := by rw [← R.functor.map_comp]
          _ = R.functor.map (barMuAtPos T n k (L.functor.obj a) ≫
                  (monadPow T n).map (L.functor.map f)) := by rw [hμ]
          _ = R.functor.map (barMuAtPos T n k (L.functor.obj a)) ≫
                  R.functor.map ((monadPow T n).map (L.functor.map f)) := by rw [R.functor.map_comp]

@[simp] lemma barFaceApp_right (n : ℕ) (a : A) :
    barFaceApp n ⟨0, by omega⟩ a = rightActionPow T R n (L.functor.obj a) := rfl

@[simp] lemma barFace_right (n : ℕ) (a : A) :
    (barFace n ⟨0, by omega⟩).app a = rightActionPow T R n (L.functor.obj a) := rfl

@[simp] lemma barFaceApp_left (n : ℕ) (a : A) :
    barFaceApp n ⟨n + 1, by omega⟩ a =
      R.functor.map ((monadPow T n).map (L.action.app a)) := by
  have h0 : ¬ ((⟨n + 1, by omega⟩ : Fin (n + 2)).val = 0) := by simp
  have hlast : ((⟨n + 1, by omega⟩ : Fin (n + 2)).val = n + 1) := rfl
  unfold barFaceApp
  rw [dite_eq_right h0, dite_eq_left hlast]

@[simp] lemma barFace_left (n : ℕ) (a : A) :
    (barFace n ⟨n + 1, by omega⟩).app a =
      R.functor.map ((monadPow T n).map (L.action.app a)) := by
  change barFaceApp n ⟨n + 1, by omega⟩ a = _
  rw [barFaceApp_left]

@[simp] lemma barFaceApp_middle (n : ℕ) (i : Fin n) (a : A) :
    barFaceApp n ⟨i.val + 1, Nat.lt_trans (Nat.succ_lt_succ i.isLt) (Nat.lt_succ_self _)⟩ a =
      R.functor.map (barMuAtPos T n i (L.functor.obj a)) := by
  have hi := i.isLt
  have h0 : ¬ ((⟨i.val + 1, Nat.lt_trans (Nat.succ_lt_succ hi) (Nat.lt_succ_self _)⟩ :
      Fin (n + 2)).val = 0) := by
    simp
  have hlast : ¬ ((⟨i.val + 1, Nat.lt_trans (Nat.succ_lt_succ hi) (Nat.lt_succ_self _)⟩ :
      Fin (n + 2)).val = n + 1) := by
    intro h
    have hle : i.val + 1 ≤ n := Nat.succ_le_of_lt hi
    have hlt : i.val + 1 < n + 1 :=
      Nat.lt_of_le_of_lt hle (Nat.lt_succ_self n)
    exact Nat.ne_of_lt hlt h
  have hk_eq : (⟨(⟨i.val + 1, Nat.lt_trans (Nat.succ_lt_succ hi) (Nat.lt_succ_self _)⟩ :
      Fin (n + 2)).val - 1, hi⟩ : Fin n) = i := by
    apply Fin.ext
    simp
  simp only [barFaceApp, dite_eq_right h0, dite_eq_right hlast, hk_eq]

@[simp] lemma barFace_middle (n : ℕ) (i : Fin n) (a : A) :
    (barFace n ⟨i.val + 1, Nat.lt_trans (Nat.succ_lt_succ i.isLt) (Nat.lt_succ_self _)⟩).app a =
      R.functor.map (barMuAtPos T n i (L.functor.obj a)) := by
  simp only [barFace, barFaceApp_middle]

/-- Public degeneracy `s_i : B_n ⟶ B_{n+1}` via `barEtaAtPos` with reversed public index. -/
noncomputable def barDegeneracy (n : ℕ) (i : Fin (n + 1)) :
    barObj T R L n ⟶ barObj T R L (n + 1) where
  app a := R.functor.map (barEtaAtPos T n i (L.functor.obj a))
  naturality a b f := by
    have hF : (barObj T R L n).map f =
        R.functor.map ((monadPow T n).map (L.functor.map f)) := rfl
    have hG : (barObj T R L (n + 1)).map f =
        R.functor.map ((monadPow T (n + 1)).map (L.functor.map f)) := rfl
    rw [hF, hG]
    have hη := barEtaAtPos_naturality T n i (f := L.functor.map f)
    calc
      R.functor.map ((monadPow T n).map (L.functor.map f)) ≫
          R.functor.map (barEtaAtPos T n i (L.functor.obj b))
          = R.functor.map ((monadPow T n).map (L.functor.map f) ≫
              barEtaAtPos T n i (L.functor.obj b)) := by
            rw [← R.functor.map_comp]
      _ = R.functor.map (barEtaAtPos T n i (L.functor.obj a) ≫
            (monadPow T (n + 1)).map (L.functor.map f)) := by rw [hη]
      _ = R.functor.map (barEtaAtPos T n i (L.functor.obj a)) ≫
            R.functor.map ((monadPow T (n + 1)).map (L.functor.map f)) := by rw [R.functor.map_comp]

@[simp] lemma barDegeneracy_app (n : ℕ) (i : Fin (n + 1)) (a : A) :
    (barDegeneracy n i).app a = R.functor.map (barEtaAtPos T n i (L.functor.obj a)) := rfl

end Elementary

section MuComp

variable {T : Monad C}

lemma muAtPos_zero_eq (n : ℕ) (X : C) :
    muAtPos T (n + 1) ⟨0, by omega⟩ X = (monadPow T n).map (T.μ.app X) := rfl

lemma muAtPos_succ_eq (n : ℕ) (k : Fin n) (X : C) :
    muAtPos T (n + 1) ⟨k.val + 1, by omega⟩ X = muAtPos T n k (T.obj X) := by
  have : (⟨k.val, by omega⟩ : Fin n) = k := by
    ext; rfl
  calc muAtPos T (n + 1) ⟨k.val + 1, by omega⟩ X = muAtPos T n ⟨k.val, by omega⟩ (T.obj X) := rfl
    _ = muAtPos T n k (T.obj X) := by rw [this]

theorem muAtPos_adjacent (n : ℕ) (k : Fin n) (X : C) :
    muAtPos T (n + 1) ⟨k.val + 1, by omega⟩ X ≫ muAtPos T n k X =
    muAtPos T (n + 1) ⟨k.val, by omega⟩ X ≫ muAtPos T n k X := by
  induction n generalizing X with
  | zero => exact Fin.elim0 k
  | succ n ih =>
    match k with
    | ⟨0, _⟩ =>
      have h1 : muAtPos T (n + 1 + 1) ⟨0 + 1, by omega⟩ X =
          (monadPow T n).map (T.μ.app (T.obj X)) := rfl
      have h2 : muAtPos T (n + 1) ⟨0, by omega⟩ X =
          (monadPow T n).map (T.μ.app X) := rfl
      have h3 : muAtPos T (n + 1 + 1) ⟨0, by omega⟩ X =
          (monadPow T (n + 1)).map (T.μ.app X) := rfl
      rw [h1, h2, h3]
      calc
        (monadPow T n).map (T.μ.app (T.obj X)) ≫ (monadPow T n).map (T.μ.app X)
            = (monadPow T n).map (T.μ.app (T.obj X) ≫ T.μ.app X) := by
              rw [← (monadPow T n).map_comp]
        _ = (monadPow T n).map (T.map (T.μ.app X) ≫ T.μ.app X) := by
              rw [T.assoc X]
        _ = (monadPow T n).map (T.map (T.μ.app X)) ≫ (monadPow T n).map (T.μ.app X) := by
              rw [(monadPow T n).map_comp]
    | ⟨k + 1, hk⟩ =>
      let k0 : Fin n := ⟨k, by omega⟩
      have hA : muAtPos T (n + 1 + 1) ⟨k + 1 + 1, by omega⟩ X =
          muAtPos T (n + 1) ⟨k + 1, by omega⟩ (T.obj X) := rfl
      have hB : muAtPos T (n + 1) ⟨k + 1, by omega⟩ X =
          muAtPos T n k0 (T.obj X) := rfl
      have hC : muAtPos T (n + 1 + 1) ⟨k + 1, by omega⟩ X =
          muAtPos T (n + 1) ⟨k0.val, by omega⟩ (T.obj X) := rfl
      calc
        muAtPos T (n + 1 + 1) ⟨k + 1 + 1, by omega⟩ X ≫ muAtPos T (n + 1) ⟨k + 1, by omega⟩ X
            = muAtPos T (n + 1) ⟨k + 1, by omega⟩ (T.obj X) ≫ muAtPos T n k0 (T.obj X) := by
              rw [hA, hB]
        _ = muAtPos T (n + 1) ⟨k0.val + 1, by omega⟩ (T.obj X) ≫ muAtPos T n k0 (T.obj X) := rfl
        _ = muAtPos T (n + 1) ⟨k0.val, by omega⟩ (T.obj X) ≫
            muAtPos T n k0 (T.obj X) := ih k0 (T.obj X)
        _ = muAtPos T (n + 1 + 1) ⟨k + 1, by omega⟩ X ≫ muAtPos T (n + 1) ⟨k + 1, by omega⟩ X := by
              rw [← hB, ← hC]

theorem muAtPos_separated (n : ℕ) (i : Fin n) (j : Fin (n + 1))
    (h : i.val + 1 < j.val) (X : C) :
    muAtPos T (n + 1) j X ≫ muAtPos T n i X =
    muAtPos T (n + 1) ⟨i.val, by omega⟩ X ≫ muAtPos T n ⟨j.val - 1, by omega⟩ X := by
  induction n generalizing X with
  | zero =>
    exact Fin.elim0 i
  | succ n ih =>
    have hj_pos : 0 < j.val := by omega
    let j0 : Fin (n + 1) := ⟨j.val - 1, by omega⟩
    have hj_eq : j = ⟨j0.val + 1, by omega⟩ := by
      apply Fin.ext; simp [j0]; omega
    have hmu_j : muAtPos T (n + 2) j X = muAtPos T (n + 1) j0 (T.obj X) := by
      rw [hj_eq]; exact muAtPos_succ_eq (n + 1) j0 X
    by_cases hi0 : i.val = 0
    · have hi_eq : i = ⟨0, by omega⟩ := by
        apply Fin.ext; omega
      have hj0_ge1 : 1 ≤ j0.val := by simp [j0]; omega
      let k0 : Fin n := ⟨j0.val - 1, by omega⟩
      have hj0_eq : j0 = ⟨k0.val + 1, by omega⟩ := by
        apply Fin.ext; simp [k0, j0]; omega
      have hmu_j0 : muAtPos T (n + 1) j0 X = muAtPos T n k0 (T.obj X) := by
        rw [hj0_eq]; exact muAtPos_succ_eq n k0 X
      have hmu_j0_T : muAtPos T (n + 1) j0 (T.obj X) = muAtPos T n k0 (T.obj (T.obj X)) := by
        rw [hj0_eq]; exact muAtPos_succ_eq n k0 (T.obj X)
      have hmu_i : muAtPos T (n + 1) i X = (monadPow T n).map (T.μ.app X) := by
        rw [hi_eq]; rfl
      have hmu_R1 : muAtPos T (n + 2) ⟨i.val, by omega⟩ X =
          (monadPow T (n + 1)).map (T.μ.app X) := by
        have hi0' : i.val = 0 := by omega
        have : (⟨i.val, by omega⟩ : Fin (n + 2)) = ⟨0, by omega⟩ := by
          apply Fin.ext; omega
        rw [this]; rfl
      have hR2 : muAtPos T (n + 1) ⟨j.val - 1, by omega⟩ X = muAtPos T (n + 1) j0 X := by
        have : (⟨j.val - 1, by omega⟩ : Fin (n + 1)) = j0 := by
          apply Fin.ext; simp [j0]
        rw [this]
      rw [hmu_j, hmu_i, hmu_R1, hR2, hmu_j0_T, hmu_j0]
      have h_nat := muAtPos_naturality T n k0 (f := T.μ.app X)
      exact h_nat.symm
    · have hi_ge1 : 1 ≤ i.val := by omega
      let i0 : Fin n := ⟨i.val - 1, by omega⟩
      have hi_eq : i = ⟨i0.val + 1, by omega⟩ := by
        apply Fin.ext; simp [i0]; omega
      have hj0_cond : i0.val + 1 < j0.val := by simp [i0, j0]; omega
      have hmu_i : muAtPos T (n + 1) i X = muAtPos T n i0 (T.obj X) := by
        rw [hi_eq]; exact muAtPos_succ_eq n i0 X
      have hR1 : muAtPos T (n + 2) ⟨i.val, by omega⟩ X =
          muAtPos T (n + 1) ⟨i0.val, by omega⟩ (T.obj X) := by
        have : (⟨i.val, by omega⟩ : Fin (n + 2)) = ⟨i0.val + 1, by omega⟩ := by
          apply Fin.ext; simp [i0]; omega
        rw [this]
        exact muAtPos_succ_eq (n + 1) ⟨i0.val, by omega⟩ X
      have hR2 : muAtPos T (n + 1) ⟨j.val - 1, by omega⟩ X = muAtPos T (n + 1) j0 X := by
        have : (⟨j.val - 1, by omega⟩ : Fin (n + 1)) = j0 := by
          apply Fin.ext; simp [j0]
        rw [this]
      have hj0_ge1 : 1 ≤ j0.val := by have := hj0_cond; omega
      let k0 : Fin n := ⟨j0.val - 1, by omega⟩
      have hj0_eq : j0 = ⟨k0.val + 1, by omega⟩ := by
        apply Fin.ext; simp [k0, j0]; omega
      have hmu_j0 : muAtPos T (n + 1) j0 X = muAtPos T n k0 (T.obj X) := by
        rw [hj0_eq]; exact muAtPos_succ_eq n k0 X
      rw [hmu_j, hmu_i, hR1, hR2, hmu_j0]
      have ih_eq := ih i0 j0 hj0_cond (T.obj X)
      have h_eq2 : muAtPos T n ⟨j0.val - 1, by omega⟩ (T.obj X) = muAtPos T n k0 (T.obj X) := by
        have : (⟨j0.val - 1, by omega⟩ : Fin n) = k0 := by
          apply Fin.ext; simp [k0]
        rw [this]
      rw [h_eq2] at ih_eq
      exact ih_eq

/--
Unified face–face law for `muAtPos`: for `i ≤ j : Fin n`,
`d_i d_j` versus `d_j d_i` in the clean `succ`/`castSucc` indexing.
`i = j` is `muAtPos_adjacent`, `i < j` is `muAtPos_separated`.
-/
theorem muAtPos_face_face (n : ℕ) (i j : Fin n) (h : i ≤ j) (X : C) :
    muAtPos T (n + 1) j.succ X ≫ muAtPos T n i X =
    muAtPos T (n + 1) i.castSucc X ≫ muAtPos T n j X := by
  by_cases hij : i = j
  · subst hij
    have h_succ : i.succ = (⟨i.val + 1, by omega⟩ : Fin (n + 1)) := by
      apply Fin.ext; simp
    have h_cast : (⟨i.val, by omega⟩ : Fin (n + 1)) = i.castSucc := by
      apply Fin.ext; simp
    have h_adj := muAtPos_adjacent (T := T) n i X
    calc
      muAtPos T (n + 1) i.succ X ≫ muAtPos T n i X =
          muAtPos T (n + 1) (⟨i.val + 1, by omega⟩ : Fin (n + 1)) X ≫
            muAtPos T n i X := by
        rw [h_succ]
      _ = muAtPos T (n + 1) (⟨i.val, by omega⟩ : Fin (n + 1)) X ≫
            muAtPos T n i X := h_adj
      _ = muAtPos T (n + 1) i.castSucc X ≫ muAtPos T n i X := by
        rw [h_cast]
  · have h_le : i.val ≤ j.val := h
    have h_ne : i.val ≠ j.val := by
      intro heq
      apply hij
      apply Fin.ext
      exact heq
    have h_lt_val : i.val < j.val := Nat.lt_of_le_of_ne h_le h_ne
    have h_lt : i.val + 1 < j.succ.val := by
      simp
      omega
    have h_sep := muAtPos_separated (T := T) n i j.succ h_lt X
    have h_cast : (⟨i.val, by omega⟩ : Fin (n + 1)) = i.castSucc := by
      apply Fin.ext; simp
    have h_j : (⟨j.succ.val - 1, by omega⟩ : Fin n) = j := by
      apply Fin.ext
      simp
    calc
      muAtPos T (n + 1) j.succ X ≫ muAtPos T n i X =
          muAtPos T (n + 1) (⟨i.val, by omega⟩ : Fin (n + 1)) X ≫
            muAtPos T n (⟨j.succ.val - 1, by omega⟩ : Fin n) X :=
        h_sep
      _ = muAtPos T (n + 1) i.castSucc X ≫
            muAtPos T n (⟨j.succ.val - 1, by omega⟩ : Fin n) X := by
        rw [h_cast]
      _ = muAtPos T (n + 1) i.castSucc X ≫ muAtPos T n j X := by
        rw [h_j]

end MuComp

section EtaComp

variable {T : Monad C}

lemma etaAtPos_zero_eq (n : ℕ) (X : C) :
    etaAtPos T (n + 1) ⟨0, by omega⟩ X = (monadPow T (n + 1)).map (T.η.app X) := rfl

lemma etaAtPos_succ_eq (n : ℕ) (k : Fin (n + 1)) (X : C) :
    etaAtPos T (n + 1) ⟨k.val + 1, by omega⟩ X = etaAtPos T n k (T.obj X) := rfl

theorem etaAtPos_deg_deg (n : ℕ) (i j : Fin (n + 1)) (h : i ≤ j) (X : C) :
    etaAtPos T n j X ≫ etaAtPos T (n + 1) i.castSucc X =
    etaAtPos T n i X ≫ etaAtPos T (n + 1) j.succ X := by
  induction n generalizing X with
  | zero =>
    have hi0 : i.val = 0 := by have := i.isLt; omega
    have hj0 : j.val = 0 := by have := j.isLt; omega
    have hi_eq : i = ⟨0, by omega⟩ := by ext; exact hi0
    have hj_eq : j = ⟨0, by omega⟩ := by ext; exact hj0
    rw [hi_eq, hj_eq]
    have hcs : (Fin.castSucc (⟨0, by omega⟩ : Fin 1) : Fin 2) = ⟨0, by omega⟩ := by
      ext; simp
    have hs : (Fin.succ (⟨0, by omega⟩ : Fin 1) : Fin 2) = ⟨1, by omega⟩ := by
      ext; simp
    rw [hcs, hs]
    simp only [etaAtPos]
    have hnat : T.η.app X ≫ T.η.app (T.obj X) = T.η.app X ≫ T.map (T.η.app X) := by
      simpa using T.η.naturality (T.η.app X)
    calc
      T.η.app X ≫ T.map (T.η.app X)
          = T.η.app X ≫ T.η.app (T.obj X) := by rw [← hnat]
      _ = T.η.app X ≫ T.η.app (T.obj X) := rfl
  | succ n ih =>
    by_cases hi0 : i.val = 0
    · have hi_eq : i = ⟨0, by omega⟩ := by ext; omega
      rw [hi_eq]
      by_cases hj0 : j.val = 0
      · have hj_eq : j = ⟨0, by omega⟩ := by ext; omega
        rw [hj_eq]
        have hcs0 : (Fin.castSucc (⟨0, by omega⟩ : Fin (n + 2)) : Fin (n + 3)) = ⟨0, by omega⟩ := by
          ext; simp
        have hs0 : (Fin.succ (⟨0, by omega⟩ : Fin (n + 2)) : Fin (n + 3)) = ⟨1, by omega⟩ := by
          ext; simp
        rw [hcs0, hs0]
        have inner : T.η.app X ≫ T.map (T.η.app X) = T.η.app X ≫ T.η.app (T.obj X) := by
          simpa using (T.η.naturality (T.η.app X)).symm
        calc
          etaAtPos T (n + 1) ⟨0, by omega⟩ X ≫ etaAtPos T (n + 2) ⟨0, by omega⟩ X
              = (monadPow T (n + 1)).map (T.η.app X) ≫
                (monadPow T (n + 2)).map (T.η.app X) := rfl
          _ = (monadPow T (n + 1)).map (T.η.app X) ≫
                (monadPow T (n + 1)).map (T.map (T.η.app X)) := rfl
          _ = (monadPow T (n + 1)).map (T.η.app X ≫ T.map (T.η.app X)) := by
                rw [← (monadPow T (n + 1)).map_comp]
          _ = (monadPow T (n + 1)).map (T.η.app X ≫ T.η.app (T.obj X)) := by
                rw [inner]
          _ = (monadPow T (n + 1)).map (T.η.app X) ≫
                (monadPow T (n + 1)).map (T.η.app (T.obj X)) := by
                rw [(monadPow T (n + 1)).map_comp]
          _ = etaAtPos T (n + 1) ⟨0, by omega⟩ X ≫
                etaAtPos T (n + 2) ⟨1, by omega⟩ X := rfl
      · have hj_pos : 0 < j.val := by omega
        let j0 : Fin (n + 1) := ⟨j.val - 1, by omega⟩
        have hj_eq : j = ⟨j0.val + 1, by omega⟩ := by
          apply Fin.ext; simp [j0]; omega
        rw [hj_eq]
        have hcs0 : (Fin.castSucc (⟨0, by omega⟩ : Fin (n + 2)) : Fin (n + 3)) = ⟨0, by omega⟩ := by
          ext; simp
        rw [hcs0]
        have h_eta_j : etaAtPos T (n + 1) ⟨j0.val + 1, by omega⟩ X =
            etaAtPos T n j0 (T.obj X) := rfl
        have h_succ_j_eq : (Fin.succ ⟨j0.val + 1, by omega⟩ : Fin (n + 3)) =
            ⟨j0.val + 2, by omega⟩ := by
          ext; simp
        calc
          etaAtPos T (n + 1) ⟨j0.val + 1, by omega⟩ X ≫ etaAtPos T (n + 2) ⟨0, by omega⟩ X
              = etaAtPos T n j0 (T.obj X) ≫ (monadPow T (n + 1)).map (T.map (T.η.app X)) := by
                rw [h_eta_j]; rfl
          _ = (monadPow T n).map (T.map (T.η.app X)) ≫ etaAtPos T n j0 (T.obj (T.obj X)) := by
                have h_nat := etaAtPos_naturality T n j0 (f := T.map (T.η.app X))
                exact h_nat.symm
          _ = (monadPow T (n + 1)).map (T.η.app X) ≫ etaAtPos T n j0 (T.obj (T.obj X)) := rfl
          _ = etaAtPos T (n + 1) ⟨0, by omega⟩ X ≫
                etaAtPos T (n + 1) ⟨j0.val + 1, by omega⟩ (T.obj X) := rfl
          _ = etaAtPos T (n + 1) ⟨0, by omega⟩ X ≫
                etaAtPos T (n + 2) ⟨j0.val + 2, by omega⟩ X := rfl
          _ = etaAtPos T (n + 1) ⟨0, by omega⟩ X ≫
                etaAtPos T (n + 2) (Fin.succ ⟨j0.val + 1, by omega⟩) X := by
                rw [h_succ_j_eq]
    · have hi_pos : 0 < i.val := by omega
      have hj_pos : 0 < j.val := by
        have : i.val ≤ j.val := by simpa [Fin.le_def] using h
        omega
      let i0 : Fin (n + 1) := ⟨i.val - 1, by omega⟩
      let j0 : Fin (n + 1) := ⟨j.val - 1, by omega⟩
      have hi_eq : i = ⟨i0.val + 1, by omega⟩ := by
        apply Fin.ext; simp [i0]; omega
      have hj_eq : j = ⟨j0.val + 1, by omega⟩ := by
        apply Fin.ext; simp [j0]; omega
      rw [hi_eq, hj_eq]
      have hi0_le_j0 : i0 ≤ j0 := by
        simp [Fin.le_def, i0, j0]; omega
      have h_i_cast : (Fin.castSucc ⟨i0.val + 1, by omega⟩ : Fin (n + 3)) =
          ⟨i0.val + 1, by omega⟩ := by
        ext; simp
      have h_j_succ : (Fin.succ ⟨j0.val + 1, by omega⟩ : Fin (n + 3)) = ⟨j0.val + 2, by omega⟩ := by
        ext; simp
      rw [h_i_cast, h_j_succ]
      have h_eta_j : etaAtPos T (n + 1) ⟨j0.val + 1, by omega⟩ X = etaAtPos T n j0 (T.obj X) := rfl
      have h_eta_i : etaAtPos T (n + 1) ⟨i0.val + 1, by omega⟩ X = etaAtPos T n i0 (T.obj X) := rfl
      have h_eta_i_cast : etaAtPos T (n + 2) ⟨i0.val + 1, by omega⟩ X =
          etaAtPos T (n + 1) i0.castSucc (T.obj X) := by
        have h1 : (⟨i0.val + 1, by omega⟩ : Fin (n + 3)) = (Fin.castSucc i0).succ := by
          ext; simp [Fin.castSucc, Fin.succ]
        rw [h1]; rfl
      have h_eta_j_succ : etaAtPos T (n + 2) ⟨j0.val + 2, by omega⟩ X =
          etaAtPos T (n + 1) ⟨j0.val + 1, by omega⟩ (T.obj X) := rfl
      have h_j_eq : (⟨j0.val + 1, by omega⟩ : Fin (n + 2)) = j0.succ := by
        ext; simp [Fin.succ]
      calc
        etaAtPos T (n + 1) ⟨j0.val + 1, by omega⟩ X ≫ etaAtPos T (n + 2) ⟨i0.val + 1, by omega⟩ X
            = etaAtPos T n j0 (T.obj X) ≫ etaAtPos T (n + 1) i0.castSucc (T.obj X) := by
              rw [h_eta_j, h_eta_i_cast]
        _ = etaAtPos T n i0 (T.obj X) ≫ etaAtPos T (n + 1) j0.succ (T.obj X) := by
              exact ih i0 j0 hi0_le_j0 (T.obj X)
        _ = etaAtPos T n i0 (T.obj X) ≫ etaAtPos T (n + 1) ⟨j0.val + 1, by omega⟩ (T.obj X) := by
              rw [h_j_eq]
        _ = etaAtPos T (n + 1) ⟨i0.val + 1, by omega⟩ X ≫
              etaAtPos T (n + 2) ⟨j0.val + 2, by omega⟩ X := by
              rw [h_eta_i, h_eta_j_succ]

end EtaComp

section EtaMu

variable {T : Monad C}

theorem etaAtPos_castSucc_muAtPos (n : ℕ) (i : Fin n) (X : C) :
    etaAtPos T n i.castSucc X ≫ muAtPos T n i X = 𝟙 _ := by
  induction n generalizing X with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    have hiv : i.val < n + 1 := i.isLt
    by_cases h0 : i.val = 0
    · have hi_eq : i = ⟨0, by omega⟩ := by ext; omega
      rw [hi_eq]
      have hcast0 : (Fin.castSucc (⟨0, by omega⟩ : Fin (n + 1)) : Fin (n + 2)) = ⟨0, by omega⟩ := by
        ext; simp
      have hmu0 : muAtPos T (n + 1) (⟨0, by omega⟩ : Fin (n + 1)) X =
          (monadPow T n).map (T.μ.app X) := rfl
      have heta0 : etaAtPos T (n + 1) (⟨0, by omega⟩ : Fin (n + 2)) X =
          (monadPow T (n + 1)).map (T.η.app X) := rfl
      calc
        etaAtPos T (n + 1) (Fin.castSucc (⟨0, by omega⟩ : Fin (n + 1))) X ≫
            muAtPos T (n + 1) (⟨0, by omega⟩ : Fin (n + 1)) X
            = etaAtPos T (n + 1) (⟨0, by omega⟩ : Fin (n + 2)) X ≫
              (monadPow T n).map (T.μ.app X) := by
          rw [hcast0, hmu0]
        _ = (monadPow T (n + 1)).map (T.η.app X) ≫
            (monadPow T n).map (T.μ.app X) := by
          rw [heta0]
        _ = (monadPow T n).map (T.map (T.η.app X)) ≫
            (monadPow T n).map (T.μ.app X) := rfl
        _ = (monadPow T n).map (T.map (T.η.app X) ≫ T.μ.app X) := by
          rw [← (monadPow T n).map_comp]
        _ = (monadPow T n).map (𝟙 _) := by
          rw [T.right_unit X]
          simp only [Functor.id_obj]
        _ = 𝟙 _ := by
          rw [(monadPow T n).map_id]
    · have hpos : 0 < i.val := by omega
      set i0 : Fin n := ⟨i.val - 1, by omega⟩ with hi0_def
      have hi_eq : i = ⟨i0.val + 1, by omega⟩ := by
        ext; simp [hi0_def]; omega
      rw [hi_eq]
      have hcast_eq : (Fin.castSucc (⟨i0.val + 1, by omega⟩ : Fin (n + 1)) : Fin (n + 2)) =
          ⟨i0.val + 1, by omega⟩ := by
        ext; simp
      have hmu_succ : muAtPos T (n + 1) (⟨i0.val + 1, by omega⟩ : Fin (n + 1)) X =
          muAtPos T n i0 (T.obj X) :=
        muAtPos_succ_eq n i0 X
      have heta_cast : etaAtPos T (n + 1) (⟨i0.val + 1, by omega⟩ : Fin (n + 2)) X =
          etaAtPos T n i0.castSucc (T.obj X) := by
        have hcs : (i0.castSucc : Fin (n + 1)) = ⟨i0.val, by omega⟩ := by
          ext; simp [hi0_def]
        calc
          etaAtPos T (n + 1) ⟨i0.val + 1, by omega⟩ X =
              etaAtPos T n ⟨i0.val, by omega⟩ (T.obj X) := rfl
          _ = etaAtPos T n i0.castSucc (T.obj X) := by
            have : (⟨i0.val, by omega⟩ : Fin (n + 1)) = i0.castSucc := by
              ext; simp [hi0_def]
            rw [this]
      calc
        etaAtPos T (n + 1) (Fin.castSucc ⟨i0.val + 1, by omega⟩) X ≫
            muAtPos T (n + 1) ⟨i0.val + 1, by omega⟩ X
            = etaAtPos T (n + 1) ⟨i0.val + 1, by omega⟩ X ≫
              muAtPos T (n + 1) ⟨i0.val + 1, by omega⟩ X := by
          rw [hcast_eq]
        _ = etaAtPos T n i0.castSucc (T.obj X) ≫ muAtPos T n i0 (T.obj X) := by
          rw [heta_cast, hmu_succ]
        _ = 𝟙 _ := ih i0 (T.obj X)

theorem etaAtPos_succ_muAtPos (n : ℕ) (i : Fin n) (X : C) :
    etaAtPos T n i.succ X ≫ muAtPos T n i X = 𝟙 _ := by
  induction n generalizing X with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    have hiv : i.val < n + 1 := i.isLt
    by_cases h0 : i.val = 0
    · have hi_eq : i = ⟨0, by omega⟩ := by ext; omega
      rw [hi_eq]
      have hsucc0 : (Fin.succ (⟨0, by omega⟩ : Fin (n + 1)) : Fin (n + 2)) = ⟨1, by omega⟩ := by
        ext; simp
      have hmu0 : muAtPos T (n + 1) (⟨0, by omega⟩ : Fin (n + 1)) X =
          (monadPow T n).map (T.μ.app X) := rfl
      have heta_succ0 : etaAtPos T (n + 1) (⟨1, by omega⟩ : Fin (n + 2)) X =
          etaAtPos T n (⟨0, by omega⟩ : Fin (n + 1)) (T.obj X) := rfl
      have heta_map : etaAtPos T n (⟨0, by omega⟩ : Fin (n + 1)) (T.obj X) =
          (monadPow T n).map (T.η.app (T.obj X)) := by
        cases n with
        | zero => rfl
        | succ _ => rfl
      calc
        etaAtPos T (n + 1) (Fin.succ (⟨0, by omega⟩ : Fin (n + 1))) X ≫
            muAtPos T (n + 1) (⟨0, by omega⟩ : Fin (n + 1)) X
            = etaAtPos T (n + 1) ⟨1, by omega⟩ X ≫ (monadPow T n).map (T.μ.app X) := by
          rw [hsucc0, hmu0]
        _ = etaAtPos T n ⟨0, by omega⟩ (T.obj X) ≫ (monadPow T n).map (T.μ.app X) := by
          rw [heta_succ0]
        _ = (monadPow T n).map (T.η.app (T.obj X)) ≫ (monadPow T n).map (T.μ.app X) := by
          rw [heta_map]
        _ = (monadPow T n).map (T.η.app (T.obj X) ≫ T.μ.app X) := by
          rw [← (monadPow T n).map_comp]
        _ = (monadPow T n).map (𝟙 _) := by
          rw [T.left_unit X]
          simp only [Functor.id_obj]
        _ = 𝟙 _ := by
          rw [(monadPow T n).map_id]
    · have hpos : 0 < i.val := by omega
      set i0 : Fin n := ⟨i.val - 1, by omega⟩ with hi0_def
      have hi_eq : i = ⟨i0.val + 1, by omega⟩ := by
        ext; simp [hi0_def]; omega
      rw [hi_eq]
      have hsucc_eq : (Fin.succ ⟨i0.val + 1, by omega⟩ : Fin (n + 2)) =
          ⟨i0.val + 2, by omega⟩ := by
        ext; simp
      have hmu_succ : muAtPos T (n + 1) ⟨i0.val + 1, by omega⟩ X =
          muAtPos T n i0 (T.obj X) :=
        muAtPos_succ_eq n i0 X
      have heta_succ2 : etaAtPos T (n + 1) ⟨i0.val + 2, by omega⟩ X =
          etaAtPos T n i0.succ (T.obj X) := by
        have h1 : etaAtPos T (n + 1) ⟨i0.val + 1 + 1, by omega⟩ X =
            etaAtPos T n ⟨i0.val + 1, by omega⟩ (T.obj X) := rfl
        have h2 : (i0.succ : Fin (n + 1)) = ⟨i0.val + 1, by omega⟩ := by
          ext; simp [Fin.succ, hi0_def]
        have heq : (⟨i0.val + 2, by omega⟩ : Fin (n + 2)) = ⟨i0.val + 1 + 1, by omega⟩ := by
          ext; rfl
        calc
          etaAtPos T (n + 1) ⟨i0.val + 2, by omega⟩ X
              = etaAtPos T (n + 1) ⟨i0.val + 1 + 1, by omega⟩ X := by
            rw [heq]
          _ = etaAtPos T n ⟨i0.val + 1, by omega⟩ (T.obj X) := h1
          _ = etaAtPos T n i0.succ (T.obj X) := by rw [← h2]
      calc
        etaAtPos T (n + 1) (Fin.succ ⟨i0.val + 1, by omega⟩) X ≫
            muAtPos T (n + 1) ⟨i0.val + 1, by omega⟩ X
            = etaAtPos T (n + 1) ⟨i0.val + 2, by omega⟩ X ≫ muAtPos T n i0 (T.obj X) := by
          rw [hsucc_eq, hmu_succ]
        _ = etaAtPos T n i0.succ (T.obj X) ≫ muAtPos T n i0 (T.obj X) := by
          rw [heta_succ2]
        _ = 𝟙 _ := ih i0 (T.obj X)

theorem etaAtPos_succ_muAtPos_castSucc_of_lt (n : ℕ) (i : Fin n) (j : Fin (n + 1))
    (h : i.val < j.val) (X : C) :
    etaAtPos T (n + 1) j.succ X ≫ muAtPos T (n + 1) i.castSucc X =
    muAtPos T n i X ≫ etaAtPos T n j X := by
  induction n generalizing X with
  | zero => exact isEmptyElim i
  | succ n ih =>
    have hj_pos : 0 < j.val := by
      have : 0 ≤ i.val := Nat.zero_le _
      omega
    have hj_sub : j.val - 1 < n + 1 := by omega
    let j0 : Fin (n + 1) := ⟨j.val - 1, hj_sub⟩
    have hj_eq : j = j0.succ := by
      apply Fin.ext
      simp [j0, Fin.succ]
      omega
    by_cases hi0 : i.val = 0
    · have hi_eq : i = ⟨0, Nat.succ_pos n⟩ := by
        apply Fin.ext
        omega
      have hi_cast_zero : (⟨0, Nat.succ_pos n⟩ : Fin (n + 1)).castSucc =
          (⟨0, Nat.succ_pos (n + 1)⟩ : Fin (n + 2)) := by
        apply Fin.ext; simp
      have h_eta_j0_T : etaAtPos T (n + 1) j0.succ (T.obj X) =
          etaAtPos T n j0 (T.obj (T.obj X)) := rfl
      have h_mu_zero : muAtPos T (n + 2)
          (⟨0, Nat.succ_pos (n + 1)⟩ : Fin (n + 2)) X =
          (monadPow T (n + 1)).map (T.μ.app X) := rfl
      have h_mu_zero' : muAtPos T (n + 1)
          (⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) X =
          (monadPow T n).map (T.μ.app X) := rfl
      have h_eta_j0 : etaAtPos T (n + 1) j0.succ X = etaAtPos T n j0 (T.obj X) := rfl
      have hi_cast_eq : i.castSucc = (⟨0, Nat.succ_pos (n + 1)⟩ : Fin (n + 2)) := by
        rw [hi_eq]
        exact hi_cast_zero
      calc
        etaAtPos T (n + 2) j.succ X ≫ muAtPos T (n + 2) i.castSucc X
            = etaAtPos T (n + 2) (j0.succ.succ) X ≫
              muAtPos T (n + 2) (⟨0, Nat.succ_pos (n + 1)⟩ : Fin (n + 2)) X := by
          rw [hj_eq, hi_cast_eq]
        _ = etaAtPos T n j0 (T.obj (T.obj X)) ≫ (monadPow T (n + 1)).map (T.μ.app X) := rfl
        _ = (monadPow T n).map (T.μ.app X) ≫ etaAtPos T n j0 (T.obj X) := by
          have hnat := etaAtPos_naturality T n j0 (f := T.μ.app X)
          exact hnat.symm
        _ = muAtPos T (n + 1) (⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) X ≫
            etaAtPos T (n + 1) j0.succ X := by
          rw [h_mu_zero', h_eta_j0]
        _ = muAtPos T (n + 1) i X ≫ etaAtPos T (n + 1) j X := by
          rw [hi_eq, hj_eq]
    · have hi_pos : 0 < i.val := by omega
      have hi_sub : i.val - 1 < n := by omega
      let i0 : Fin n := ⟨i.val - 1, hi_sub⟩
      have hi_eq : i = i0.succ := by
        apply Fin.ext
        simp [i0, Fin.succ]
        omega
      have hi_lt_j0 : i0.val < j0.val := by
        have : i.val < j.val := h
        have : i0.val + 1 < j0.val + 1 := by
          calc i0.val + 1 = i.val := by simp [i0]; omega
            _ < j.val := h
            _ = j0.val + 1 := by simp [j0]; omega
        omega
      have hi_cast_eq : i.castSucc = (i0.castSucc).succ := by
        apply Fin.ext
        simp [i0, Fin.castSucc, Fin.succ]
        omega
      have h_eta_succ : etaAtPos T (n + 2) j.succ X = etaAtPos T (n + 1) j (T.obj X) := rfl
      have h_mu_cast_succ : muAtPos T (n + 2) i.castSucc X =
          muAtPos T (n + 1) i0.castSucc (T.obj X) := by
        rw [hi_cast_eq]
        rfl
      have h_mu_succ : muAtPos T (n + 1) i X = muAtPos T n i0 (T.obj X) := by
        rw [hi_eq]
        rfl
      have h_eta_j : etaAtPos T (n + 1) j X = etaAtPos T n j0 (T.obj X) := by
        rw [hj_eq]
        rfl
      calc
        etaAtPos T (n + 2) j.succ X ≫ muAtPos T (n + 2) i.castSucc X
            = etaAtPos T (n + 1) j (T.obj X) ≫ muAtPos T (n + 1) i0.castSucc (T.obj X) := by
          rw [h_eta_succ, h_mu_cast_succ]
        _ = etaAtPos T (n + 1) j0.succ (T.obj X) ≫ muAtPos T (n + 1) i0.castSucc (T.obj X) := by
          rw [hj_eq]
        _ = muAtPos T n i0 (T.obj X) ≫ etaAtPos T n j0 (T.obj X) := ih i0 j0 hi_lt_j0 (T.obj X)
        _ = muAtPos T (n + 1) i X ≫ etaAtPos T (n + 1) j X := by
          rw [h_mu_succ, h_eta_j]

theorem etaAtPos_castSucc_muAtPos_succ_of_le (n : ℕ) (i : Fin n) (j : Fin (n + 1))
    (h : j.val ≤ i.val) (X : C) :
    etaAtPos T (n + 1) j.castSucc X ≫ muAtPos T (n + 1) i.succ X =
    muAtPos T n i X ≫ etaAtPos T n j X := by
  induction n generalizing X with
  | zero => exact isEmptyElim i
  | succ n ih =>
    by_cases hj0 : j.val = 0
    · have hj_eq : j = ⟨0, Nat.succ_pos (n + 1)⟩ := by
        apply Fin.ext; omega
      have hj_cast_zero : (⟨0, Nat.succ_pos (n + 1)⟩ : Fin (n + 2)).castSucc =
          (⟨0, Nat.succ_pos (n + 2)⟩ : Fin (n + 3)) := by
        apply Fin.ext; simp
      have h_eta_zero : etaAtPos T (n + 2)
          (⟨0, Nat.succ_pos (n + 2)⟩ : Fin (n + 3)) X =
          (monadPow T (n + 2)).map (T.η.app X) := rfl
      have h_eta_zero' : etaAtPos T (n + 1)
          (⟨0, Nat.succ_pos (n + 1)⟩ : Fin (n + 2)) X =
          (monadPow T (n + 1)).map (T.η.app X) := rfl
      have h_mu_succ : muAtPos T (n + 2) i.succ X = muAtPos T (n + 1) i (T.obj X) := rfl
      calc
        etaAtPos T (n + 2) j.castSucc X ≫ muAtPos T (n + 2) i.succ X
            = etaAtPos T (n + 2)
                (⟨0, Nat.succ_pos (n + 2)⟩ : Fin (n + 3)) X ≫
              muAtPos T (n + 1) i (T.obj X) := by
          rw [hj_eq, hj_cast_zero, h_mu_succ]
        _ = (monadPow T (n + 2)).map (T.η.app X) ≫ muAtPos T (n + 1) i (T.obj X) := by
          rw [h_eta_zero]
        _ = muAtPos T (n + 1) i X ≫ (monadPow T (n + 1)).map (T.η.app X) := by
          have hnat := muAtPos_naturality T (n + 1) i (f := T.η.app X)
          exact hnat
        _ = muAtPos T (n + 1) i X ≫
            etaAtPos T (n + 1) (⟨0, Nat.succ_pos (n + 1)⟩ : Fin (n + 2)) X := by
          rw [h_eta_zero']
        _ = muAtPos T (n + 1) i X ≫ etaAtPos T (n + 1) j X := by
          rw [hj_eq]
    · have hj_pos : 0 < j.val := by omega
      have hj_sub : j.val - 1 < n + 1 := by omega
      let j0 : Fin (n + 1) := ⟨j.val - 1, hj_sub⟩
      have hj_eq : j = j0.succ := by
        apply Fin.ext
        simp [j0, Fin.succ]
        omega
      by_cases hi0 : i.val = 0
      · have : j.val ≤ 0 := by omega
        omega
      · have hi_sub : i.val - 1 < n := by omega
        let i0 : Fin n := ⟨i.val - 1, hi_sub⟩
        have hi_eq : i = i0.succ := by
          apply Fin.ext
          simp [i0, Fin.succ]
          omega
        have hj_le_i0 : j0.val ≤ i0.val := by
          have : j.val ≤ i.val := h
          have : j0.val + 1 ≤ i0.val + 1 := by
            calc j0.val + 1 = j.val := by simp [j0]; omega
              _ ≤ i.val := h
              _ = i0.val + 1 := by simp [i0]; omega
          omega
        have hj_cast_eq : j.castSucc = (j0.castSucc).succ := by
          apply Fin.ext
          simp [j0, Fin.castSucc, Fin.succ]
          omega
        have hi_succ_eq : i.succ = (i0.succ).succ := by
          apply Fin.ext
          simp [i0, Fin.succ]
          omega
        have h_eta_cast : etaAtPos T (n + 2) j.castSucc X =
            etaAtPos T (n + 1) j0.castSucc (T.obj X) := by
          rw [hj_cast_eq]
          rfl
        have h_mu_succ : muAtPos T (n + 2) i.succ X =
            muAtPos T (n + 1) i0.succ (T.obj X) := by
          rw [hi_succ_eq]
          rfl
        have h_mu : muAtPos T (n + 1) i X = muAtPos T n i0 (T.obj X) := by
          rw [hi_eq]
          rfl
        have h_eta : etaAtPos T (n + 1) j X = etaAtPos T n j0 (T.obj X) := by
          rw [hj_eq]
          rfl
        calc
          etaAtPos T (n + 2) j.castSucc X ≫ muAtPos T (n + 2) i.succ X
              = etaAtPos T (n + 1) j0.castSucc (T.obj X) ≫
                muAtPos T (n + 1) i0.succ (T.obj X) := by
            rw [h_eta_cast, h_mu_succ]
          _ = muAtPos T n i0 (T.obj X) ≫ etaAtPos T n j0 (T.obj X) :=
            ih i0 j0 hj_le_i0 (T.obj X)
          _ = muAtPos T (n + 1) i X ≫ etaAtPos T (n + 1) j X := by
            rw [h_mu, h_eta]

end EtaMu

end Monad
end CategoryTheory
