/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Monad.BarAugmentation
public import MathlibExt.AlgebraicTopology.SimplicialObject.DataExtraToSimplicial

/-! # Regular-right bar contraction

Mathematical source: J. P. May, *The Geometry of Iterated Loop Spaces*,
Lecture Notes in Mathematics 271, Springer, 1972, Chapter 9,
Construction 9.6 and Remark 9.12, <https://doi.org/10.1007/BFb0067491>.

May's functor-valued two-sided bar has degree `n` of the form `Y C^n X`;
here `B(R,T,L)_n = R(T^n(L(-)))`, written in Lean's diagrammatic functor
order as `L.functor ⋙ monadPow T n ⋙ R.functor`. This API publicly counts
faces from the right-module end (`d₀` is the right action and `d_{n+1}`
the left action), while the internal `muAtPos`/`etaAtPos` count from the
left-module end and `barMuAtPos`/`barEtaAtPos` apply `Fin.rev`.
The regular-right specialization has the left extra degeneracy with
distinguished `d₀`. No further homotopical consequence is claimed here.

This module specializes the general two-sided bar `B(R, T, L)` to the regular
right module `R = T`. The balanced pairing targets `L.functor` via `L.action`,
hence the augmentation `B(T, T, L) → L`. The section `s'` and operators `s n`
insert the monad unit at the outer end, giving the left extra-degeneracy and
augmentation direction (distinguished face `d₀`). All faces, degeneracies, and
balanced-pairing machinery are reused from the general bar, and the genuine
contraction consequences are inherited from Mathlib's left-handed
`SimplicialObject.Augmented.ExtraDegeneracy` by transport rather than reproved
here. This is a contraction of the underlying augmented simplicial object in
functors, not a contraction inside the Eilenberg–Moore category. -/

@[expose] public section

namespace CategoryTheory
namespace Monad

universe v₁ v₃ u₁ u₃

variable {C : Type u₁} [Category.{v₁} C]
variable {A : Type u₃} [Category.{v₃} A]
variable {T : Monad C}

namespace BarRegularContraction

variable (L : LeftModule A T)

/--
Regular-right augmentation target: the underlying functor `L.functor`,
receiving the balanced pairing from degree zero of `B(T, T, L)`.
-/
abbrev regularTarget : A ⥤ C :=
  L.functor

@[simp]
theorem regularTarget_obj (a : A) :
    (regularTarget L).obj a = L.functor.obj a :=
  rfl

@[simp]
theorem regularTarget_map {a b : A} (f : a ⟶ b) :
    (regularTarget L).map f = L.functor.map f :=
  rfl

/--
Regular-right augmentation pairing `B₀ ⟶ regularTarget L` given by `L.action`,
the degree-zero component of the `B(T, T, L) → L` augmentation.
-/
abbrev regularPairing :
    barObj T (RightModule.regular T) L 0 ⟶ regularTarget L :=
  L.action

@[simp]
theorem regularPairing_app (a : A) :
    (regularPairing L).app a = L.action.app a :=
  rfl

/--
The regular pairing respects the right and left actions, hence is balanced
for the regular-right bar `B(T, T, L)`.
-/
theorem regularPairing_isBalanced :
    IsBalancedPairing (T := T) (R := RightModule.regular T)
      (L := L) (regularPairing L) := by
  rw [isBalancedPairing_iff_action_eq]
  intro a
  simp only [regularPairing, RightModule.regular_action,
    RightModule.regular_functor]
  exact LeftModule.assoc_app L a

/--
Packaged balanced pairing for the regular-right bar: target `regularTarget L`
with pairing `regularPairing L`, supplying the `B(T, T, L) → L` augmentation.
-/
noncomputable def regularBalancedPairing :
    BalancedPairing T (RightModule.regular T) L where
  target := regularTarget L
  pairing := regularPairing L
  balanced := regularPairing_isBalanced L

@[simp]
theorem regularBalancedPairing_target :
    (regularBalancedPairing L).target = regularTarget L :=
  rfl

@[simp]
theorem regularBalancedPairing_pairing :
    (regularBalancedPairing L).pairing = regularPairing L :=
  rfl

@[simp]
theorem regularBalancedPairing_pairing_app (a : A) :
    (regularBalancedPairing L).pairing.app a = L.action.app a :=
  rfl

/--
Augmentation section `regularTarget L ⟶ B₀` inserting the unit `η`.
This is the degree-zero section of the augmentation, distinct from the degreewise
extra-degeneracy operators `s n`.
-/
noncomputable def s' : regularTarget L ⟶ barObj T (RightModule.regular T) L 0 :=
  Functor.whiskerLeft L.functor T.η

@[simp]
theorem s'_app (a : A) :
    (s' L).app a = T.η.app (L.functor.obj a) :=
  rfl

/--
Successor object unfolding for the regular-right bar: `B_{n+1} a = T.obj (B_n a)`.
Internal transport form of `monadPow_obj_T_comm` orienting the forward/backward
successor comparison; not a broad end-user entry point.
-/
theorem barObj_obj_succ_eq (n : ℕ) (a : A) :
    (barObj T (RightModule.regular T) L (n + 1)).obj a =
      T.obj ((barObj T (RightModule.regular T) L n).obj a) :=
  congrArg T.obj (monadPow_obj_T_comm T n (L.functor.obj a))

/--
Transport cancellation: `eqToHom h.symm ≫ eqToHom h = 𝟙`.
Internal rewriting helper discharging inverse-pair transports from successor comparisons.
-/
theorem eqToHom_symm_comp_eq {X Y : C} (h : X = Y) :
    eqToHom h.symm ≫ eqToHom h = 𝟙 Y := by
  cases h
  simp

/--
Transport cancellation: `eqToHom h ≫ eqToHom h.symm = 𝟙`.
Internal rewriting helper discharging forward-then-backward transports from successor
comparisons.
-/
theorem eqToHom_comp_symm_eq {X Y : C} (h : X = Y) :
    eqToHom h ≫ eqToHom h.symm = 𝟙 X := by
  cases h
  simp

/--
Successor map unfolding: the `B_{n+1}` map is forward transport ≫ `T.map`
of the `B_n` map ≫ backward transport. Internal naturality form used for the
successor forward morphism; not a broad end-user entry point.
-/
theorem barObj_map_succ_eq (n : ℕ) {a b : A} (f : a ⟶ b) :
    (barObj T (RightModule.regular T) L (n + 1)).map f =
      eqToHom (barObj_obj_succ_eq L n a) ≫
        T.map ((barObj T (RightModule.regular T) L n).map f) ≫
          eqToHom (barObj_obj_succ_eq L n b).symm := by
  have h_comm_a := monadPow_obj_T_comm T n (L.functor.obj a)
  have h_comm_b := monadPow_obj_T_comm T n (L.functor.obj b)
  have h_nat := monadPow_obj_T_comm_naturality T n (L.functor.map f)
  have h_Bn : (barObj T (RightModule.regular T) L n).map f =
      T.map ((monadPow T n).map (L.functor.map f)) := rfl
  have h_Bsucc : (barObj T (RightModule.regular T) L (n + 1)).map f =
      T.map ((monadPow T n).map (T.map (L.functor.map f))) := rfl
  have h_T0 : T.map ((monadPow T n).map (T.map (L.functor.map f)) ≫
      eqToHom h_comm_b) =
      T.map (eqToHom h_comm_a ≫ T.map ((monadPow T n).map (L.functor.map f))) :=
    congrArg T.map h_nat
  have h_T1 : T.map ((monadPow T n).map (T.map (L.functor.map f))) ≫
      T.map (eqToHom h_comm_b) =
      T.map (eqToHom h_comm_a) ≫
        T.map (T.map ((monadPow T n).map (L.functor.map f))) := by
    rw [Functor.map_comp, Functor.map_comp] at h_T0
    exact h_T0
  have h_eq_a : T.map (eqToHom h_comm_a) =
      eqToHom (congrArg T.obj h_comm_a) := eqToHom_map _ h_comm_a
  have h_eq_b : T.map (eqToHom h_comm_b) =
      eqToHom (congrArg T.obj h_comm_b) := eqToHom_map _ h_comm_b
  have h_T : T.map ((monadPow T n).map (T.map (L.functor.map f))) ≫
      eqToHom (congrArg T.obj h_comm_b) =
      eqToHom (congrArg T.obj h_comm_a) ≫
        T.map (T.map ((monadPow T n).map (L.functor.map f))) := by
    rw [← h_eq_a, ← h_eq_b]
    exact h_T1
  have h_a : (barObj T (RightModule.regular T) L (n + 1)).map f ≫
      eqToHom (congrArg T.obj h_comm_b) =
      T.map ((monadPow T n).map (T.map (L.functor.map f))) ≫
        eqToHom (congrArg T.obj h_comm_b) :=
    congrArg (· ≫ eqToHom (congrArg T.obj h_comm_b)) h_Bsucc
  have h_b : T.map ((monadPow T n).map (T.map (L.functor.map f))) ≫
      eqToHom (congrArg T.obj h_comm_b) =
      eqToHom (congrArg T.obj h_comm_a) ≫
        T.map (T.map ((monadPow T n).map (L.functor.map f))) := h_T
  have h_c : eqToHom (congrArg T.obj h_comm_a) ≫
        T.map (T.map ((monadPow T n).map (L.functor.map f))) =
      eqToHom (congrArg T.obj h_comm_a) ≫
        T.map ((barObj T (RightModule.regular T) L n).map f) :=
    congrArg (eqToHom (congrArg T.obj h_comm_a) ≫ ·)
      (congrArg T.map h_Bn.symm)
  have h_comm : (barObj T (RightModule.regular T) L (n + 1)).map f ≫
      eqToHom (congrArg T.obj h_comm_b) =
      eqToHom (congrArg T.obj h_comm_a) ≫
        T.map ((barObj T (RightModule.regular T) L n).map f) :=
    h_a.trans (h_b.trans h_c)
  have h1 : (barObj T (RightModule.regular T) L (n + 1)).map f =
      (barObj T (RightModule.regular T) L (n + 1)).map f ≫ 𝟙 _ :=
    (Category.comp_id _).symm
  have h2 : (barObj T (RightModule.regular T) L (n + 1)).map f ≫ 𝟙 _ =
      (barObj T (RightModule.regular T) L (n + 1)).map f ≫
        (eqToHom (congrArg T.obj h_comm_b) ≫
          eqToHom (congrArg T.obj h_comm_b).symm) :=
    congrArg ((barObj T (RightModule.regular T) L (n + 1)).map f ≫ ·)
      (eqToHom_comp_symm_eq (congrArg T.obj h_comm_b)).symm
  have h3 : (barObj T (RightModule.regular T) L (n + 1)).map f ≫
        (eqToHom (congrArg T.obj h_comm_b) ≫
          eqToHom (congrArg T.obj h_comm_b).symm) =
        ((barObj T (RightModule.regular T) L (n + 1)).map f ≫
          eqToHom (congrArg T.obj h_comm_b)) ≫
            eqToHom (congrArg T.obj h_comm_b).symm :=
    (Category.assoc _ _ _).symm
  have h4 : ((barObj T (RightModule.regular T) L (n + 1)).map f ≫
          eqToHom (congrArg T.obj h_comm_b)) ≫
            eqToHom (congrArg T.obj h_comm_b).symm =
        (eqToHom (congrArg T.obj h_comm_a) ≫
          T.map ((barObj T (RightModule.regular T) L n).map f)) ≫
            eqToHom (congrArg T.obj h_comm_b).symm :=
    congrArg (· ≫ eqToHom (congrArg T.obj h_comm_b).symm) h_comm
  have h5 : (eqToHom (congrArg T.obj h_comm_a) ≫
          T.map ((barObj T (RightModule.regular T) L n).map f)) ≫
            eqToHom (congrArg T.obj h_comm_b).symm =
        eqToHom (congrArg T.obj h_comm_a) ≫
          T.map ((barObj T (RightModule.regular T) L n).map f) ≫
            eqToHom (congrArg T.obj h_comm_b).symm :=
    Category.assoc _ _ _
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (by rfl)))))

/--
Postcomposed comparison target `B_n ⋙ T` for the regular-right successor.
Internal codomain presenting `B_n` with the outer `T` factored out for unit
whiskering; not a broad end-user entry point.
-/
abbrev barObjCompT (n : ℕ) : A ⥤ C :=
  barObj T (RightModule.regular T) L n ⋙ T.toFunctor

/--
Forward successor comparison `B_{n+1} ⟶ B_n ⋙ T` via `eqToHom` of the
successor object equality. Internal orientation half of the successor isomorphism.
-/
noncomputable def barObjSuccForward (n : ℕ) :
    barObj T (RightModule.regular T) L (n + 1) ⟶ barObjCompT L n where
  app a := eqToHom (barObj_obj_succ_eq L n a)
  naturality a b f := by
    have h_map := barObj_map_succ_eq L n f
    have h_symm : eqToHom (barObj_obj_succ_eq L n b).symm ≫
        eqToHom (barObj_obj_succ_eq L n b) = 𝟙 _ :=
      eqToHom_symm_comp_eq (barObj_obj_succ_eq L n b)
    calc
      (barObj T (RightModule.regular T) L (n + 1)).map f ≫
            eqToHom (barObj_obj_succ_eq L n b)
          = (eqToHom (barObj_obj_succ_eq L n a) ≫
              T.map ((barObj T (RightModule.regular T) L n).map f) ≫
                eqToHom (barObj_obj_succ_eq L n b).symm) ≫
              eqToHom (barObj_obj_succ_eq L n b) := by
        rw [h_map]
      _ = eqToHom (barObj_obj_succ_eq L n a) ≫
            T.map ((barObj T (RightModule.regular T) L n).map f) ≫
              eqToHom (barObj_obj_succ_eq L n b).symm ≫
                eqToHom (barObj_obj_succ_eq L n b) := by
        simp only [Category.assoc]
      _ = eqToHom (barObj_obj_succ_eq L n a) ≫
            T.map ((barObj T (RightModule.regular T) L n).map f) ≫
              (eqToHom (barObj_obj_succ_eq L n b).symm ≫
                eqToHom (barObj_obj_succ_eq L n b)) := by
        simp only [← Category.assoc]
      _ = eqToHom (barObj_obj_succ_eq L n a) ≫
            T.map ((barObj T (RightModule.regular T) L n).map f) ≫
              𝟙 _ := by
        rw [h_symm]
      _ = eqToHom (barObj_obj_succ_eq L n a) ≫
            T.map ((barObj T (RightModule.regular T) L n).map f) := by
        simp only [Category.comp_id]
      _ = eqToHom (barObj_obj_succ_eq L n a) ≫
            (barObjCompT L n).map f := by
        rfl

/--
Successor isomorphism `B_{n+1} ≅ B_n ⋙ T` from the successor object equality.
Internal transport packaging used to define the extra-degeneracy operators.
-/
noncomputable def barObjSuccIso (n : ℕ) :
    barObj T (RightModule.regular T) L (n + 1) ≅ barObjCompT L n :=
  NatIso.ofComponents (fun a => eqToIso (barObj_obj_succ_eq L n a))
    (fun f => (barObjSuccForward L n).naturality f)

/--
Unit whiskering `B_n ⟶ B_n ⋙ T` given by `η` at `B_n` objects.
Internal first factor of the extra-degeneracy operator `s`.
-/
noncomputable def barObjWhiskerEta (n : ℕ) :
    barObj T (RightModule.regular T) L n ⟶ barObjCompT L n :=
  Functor.whiskerLeft (barObj T (RightModule.regular T) L n) T.η

/--
Degreewise extra degeneracy `Bₙ ⟶ Bₙ₊₁` inserting the outer unit via whiskering
plus the successor isomorphism; the regular-right left extra degeneracy with
distinguished face `d₀`.
-/
noncomputable def s (n : ℕ) :
    barObj T (RightModule.regular T) L n ⟶
      barObj T (RightModule.regular T) L (n + 1) :=
  barObjWhiskerEta L n ≫ (barObjSuccIso L n).inv

/--
Component formula for the extra-degeneracy operator:
`s_n a = η_{B_n a} ≫ eqToHom (succ_eq).symm`. Internal simp form of the
whiskering-plus-backward-transport definition.
-/
@[simp]
theorem s_app (n : ℕ) (a : A) :
    (s L n).app a = T.η.app ((barObj T (RightModule.regular T) L n).obj a) ≫
      eqToHom (barObj_obj_succ_eq L n a).symm :=
  rfl

/--
First regular-right endpoint law: `s' ≫ regularPairing = 𝟙`.

The composite `regularTarget L ⟶ B₀ ⟶ regularTarget L` is
`η_{L a} ≫ L.action_a`.  By `LeftModule.unit_app` this is the identity,
so `s'` is a section of the augmentation pairing.
-/
theorem s'_comp_regularPairing :
    s' L ≫ regularPairing L = 𝟙 (regularTarget L) := by
  ext a
  simp only [NatTrans.comp_app, s'_app, regularPairing_app]
  exact LeftModule.unit_app L a

/--
Degree-zero extra-degeneracy law: `s₀ ≫ d₁ = pairing ≫ s'`.

At degree zero the successor comparison `barObj_obj_succ_eq L 0 a` is `congrArg T.obj
(monadPow_obj_T_comm T 0 _)` with `monadPow_obj_T_comm T 0 _ = rfl`.  Hence `barObj T... L 1`
object equals `T.obj (barObj T... L 0).obj` by `rfl`.  We `cases` on that object equality – an
honest use of reflexivity at degree zero – making `B₁` and `T(B₀)` definitionally equal, so
`barObj_obj_succ_eq` becomes `rfl` and `eqToHom rfl = 𝟙` via `rfl`.  Then `s L 0` reduces to
`η_{B₀}` by `comp_id`.  The face `d₁ = barFace 0 1` is the last face, i.e. `T.map (L.action)`, by
`barFaceApp_of_val_last` and `rfl`.  The equality becomes `η ≫ T.map action = action ≫ η`, which
is `T.η.naturality (L.action.app a)`.
-/
theorem s_zero_comp_barFace_last :
    s L 0 ≫ barFace (T := T) (R := RightModule.regular T) (L := L) 0 (1 : Fin 2) =
      regularPairing L ≫ s' L := by
  ext a
  -- Honest degree-zero elimination: the successor comparison is `rfl` at `n = 0`.
  -- It is `barObj_obj_succ_eq L 0 a : B₁.obj a = T.obj (B₀.obj a)`.
  have hSucc : (barObj T (RightModule.regular T) L 1).obj a =
      T.obj ((barObj T (RightModule.regular T) L 0).obj a) :=
    barObj_obj_succ_eq L 0 a
  cases hSucc
  -- Align `B₀` with `L ⋙ T` so `T.η.naturality` matches on the nose; also `rfl`.
  have hB0 : (barObj T (RightModule.regular T) L 0).obj a =
      (L.functor ⋙ T.toFunctor).obj a := rfl
  cases hB0
  have hComp : (s L 0 ≫ barFace (T := T) (R := RightModule.regular T) (L := L) 0
      (1 : Fin 2)).app a =
      (s L 0).app a ≫ (barFace (T := T) (R := RightModule.regular T) (L := L) 0
        (1 : Fin 2)).app a := rfl
  have hs : (s L 0).app a = T.η.app ((L.functor ⋙ T.toFunctor).obj a) := by
    have h1 : (s L 0).app a =
        T.η.app ((L.functor ⋙ T.toFunctor).obj a) ≫
          𝟙 (T.obj ((L.functor ⋙ T.toFunctor).obj a)) := rfl
    have h2 : T.η.app ((L.functor ⋙ T.toFunctor).obj a) ≫
          𝟙 (T.obj ((L.functor ⋙ T.toFunctor).obj a)) =
        T.η.app ((L.functor ⋙ T.toFunctor).obj a) := by
      simp only [Category.comp_id]
    exact h1.trans h2
  have hf : (barFace (T := T) (R := RightModule.regular T) (L := L) 0
      (1 : Fin 2)).app a = T.map (L.action.app a) := rfl
  have hL : (s L 0).app a ≫ (barFace (T := T) (R := RightModule.regular T) (L := L) 0
      (1 : Fin 2)).app a =
      T.η.app ((L.functor ⋙ T.toFunctor).obj a) ≫ T.map (L.action.app a) := by
    have h1 : (s L 0).app a ≫ (barFace (T := T) (R := RightModule.regular T) (L := L) 0
        (1 : Fin 2)).app a =
        T.η.app ((L.functor ⋙ T.toFunctor).obj a) ≫
          (barFace (T := T) (R := RightModule.regular T) (L := L) 0
            (1 : Fin 2)).app a :=
      congrArg (· ≫ (barFace (T := T) (R := RightModule.regular T) (L := L) 0
        (1 : Fin 2)).app a) hs
    have h2 : T.η.app ((L.functor ⋙ T.toFunctor).obj a) ≫
          (barFace (T := T) (R := RightModule.regular T) (L := L) 0
            (1 : Fin 2)).app a =
        T.η.app ((L.functor ⋙ T.toFunctor).obj a) ≫ T.map (L.action.app a) :=
      congrArg (T.η.app ((L.functor ⋙ T.toFunctor).obj a) ≫ ·) hf
    exact h1.trans h2
  have hNat : T.η.app ((L.functor ⋙ T.toFunctor).obj a) ≫ T.map (L.action.app a) =
      L.action.app a ≫ T.η.app (L.functor.obj a) :=
    (T.η.naturality (L.action.app a)).symm
  have hR : L.action.app a ≫ T.η.app (L.functor.obj a) =
      (regularPairing L ≫ s' L).app a := rfl
  exact hComp.trans (hL.trans (hNat.trans hR))

/--
Regular-right distinguished zero-face law: `s_n ≫ d₀ = 𝟙`.

At `a : A` let `X = (monadPow T n).obj (L a)` so `B_n a = T.obj X` by `rfl`.
`s` is `η_{B_n} ≫ eqToHom (barObj_obj_succ_eq).symm` by `s_app`.
The `0`-face is `barFaceApp_of_val_zero` which is `rightActionPow`.
By `rightActionPow_eq` for the regular right module `(regular T).functor = T`
and `(regular T).action = T.μ`, this face is
`T.map (eqToHom (monadPow_succ_obj_eq)) ≫ T.μ_X`.
The generic `eqToHom_map` gives `T.map (eqToHom _) = eqToHom (congrArg T.obj _)`.
The bar successor comparison `barObj_obj_succ_eq L n a` is
`congrArg T.obj (monadPow_succ_obj_eq n _)` by `rfl`
(`monadPow_succ_obj_eq = monadPow_obj_T_comm`). Hence the composite is
`η_{T X} ≫ eqToHom.symm ≫ eqToHom ≫ μ_X`.
Cancelling by `eqToHom_symm_comp_eq` yields `η_{T X} ≫ μ_X`, which is `𝟙` by
`T.left_unit`.
-/
theorem s_comp_barFace_zero (n : ℕ) :
    s L n ≫ barFace (T := T) (R := RightModule.regular T) (L := L) n
      (0 : Fin (n + 2)) = 𝟙 _ := by
  ext a
  simp only [NatTrans.comp_app, NatTrans.id_app, Functor.comp_obj]
  have h0v : (0 : Fin (n + 2)).val = 0 := rfl
  have hFaceApp0 : barFaceApp (T := T) (R := RightModule.regular T) (L := L) n
      (0 : Fin (n + 2)) a =
      rightActionPow T (RightModule.regular T) n (L.functor.obj a) :=
    barFaceApp_of_val_zero (T := T) (R := RightModule.regular T) (L := L) h0v
  have hFace0 : (barFace (T := T) (R := RightModule.regular T) (L := L) n (0 : Fin (n + 2))).app a =
      rightActionPow T (RightModule.regular T) n (L.functor.obj a) := by
    have h1 : (barFace (T := T) (R := RightModule.regular T) (L := L) n (0 : Fin (n + 2))).app a =
        barFaceApp (T := T) (R := RightModule.regular T) (L := L) n (0 : Fin (n + 2)) a := rfl
    exact h1.trans hFaceApp0
  have hPow : rightActionPow T (RightModule.regular T) n (L.functor.obj a) =
      (RightModule.regular T).functor.map
        (eqToHom (monadPow_succ_obj_eq T n (L.functor.obj a))) ≫
        (RightModule.regular T).action.app
          ((monadPow T n).obj (L.functor.obj a)) :=
    rightActionPow_eq T (RightModule.regular T) n (L.functor.obj a)
  have hReg : (RightModule.regular T).functor.map
        (eqToHom (monadPow_succ_obj_eq T n (L.functor.obj a))) ≫
        (RightModule.regular T).action.app
          ((monadPow T n).obj (L.functor.obj a)) =
      T.map (eqToHom (monadPow_succ_obj_eq T n (L.functor.obj a))) ≫
        T.μ.app ((monadPow T n).obj (L.functor.obj a)) := rfl
  have hMap : T.map (eqToHom (monadPow_succ_obj_eq T n (L.functor.obj a))) =
      eqToHom (congrArg T.obj (monadPow_succ_obj_eq T n (L.functor.obj a))) :=
    eqToHom_map (F := T.toFunctor) _
  -- Use congrArg form for the face so its codomain is (T⋙T).obj _ directly,
  -- avoiding an extra T.obj (barObj_obj) transport that triggers
  -- implicit-transparency mismatch.
  have hFaceEq :
      (barFace (T := T) (R := RightModule.regular T) (L := L) n
          (0 : Fin (n + 2))).app a =
      eqToHom (congrArg T.obj (monadPow_succ_obj_eq T n (L.functor.obj a))) ≫
        T.μ.app ((monadPow T n).obj (L.functor.obj a)) := by
    have h1 :
        (barFace (T := T) (R := RightModule.regular T) (L := L) n
            (0 : Fin (n + 2))).app a =
        rightActionPow T (RightModule.regular T) n (L.functor.obj a) := hFace0
    have h2 : rightActionPow T (RightModule.regular T) n (L.functor.obj a) =
        (RightModule.regular T).functor.map
            (eqToHom (monadPow_succ_obj_eq T n (L.functor.obj a))) ≫
          (RightModule.regular T).action.app
            ((monadPow T n).obj (L.functor.obj a)) := hPow
    have h3 :
        (RightModule.regular T).functor.map
            (eqToHom (monadPow_succ_obj_eq T n (L.functor.obj a))) ≫
          (RightModule.regular T).action.app
            ((monadPow T n).obj (L.functor.obj a)) =
        T.map (eqToHom (monadPow_succ_obj_eq T n (L.functor.obj a))) ≫
          T.μ.app ((monadPow T n).obj (L.functor.obj a)) := hReg
    have h4 :
        T.map (eqToHom (monadPow_succ_obj_eq T n (L.functor.obj a))) ≫
          T.μ.app ((monadPow T n).obj (L.functor.obj a)) =
        eqToHom (congrArg T.obj (monadPow_succ_obj_eq T n (L.functor.obj a))) ≫
          T.μ.app ((monadPow T n).obj (L.functor.obj a)) := by
      rw [hMap]
    exact h1.trans (h2.trans (h3.trans h4))
  -- s in the same congrArg form: η_{T.obj X} ≫ eqToHom (congrArg succ_eq).symm,
  -- which is rfl after unfolding barObj_obj_succ_eq and barObj_obj.
  have hs : (s L n).app a =
      T.η.app (T.obj ((monadPow T n).obj (L.functor.obj a))) ≫
        eqToHom (congrArg T.obj (monadPow_succ_obj_eq T n (L.functor.obj a))).symm := rfl
  have hComp :
      (s L n).app a ≫
        (barFace (T := T) (R := RightModule.regular T) (L := L) n
            (0 : Fin (n + 2))).app a =
      (T.η.app (T.obj ((monadPow T n).obj (L.functor.obj a))) ≫
        eqToHom (congrArg T.obj
            (monadPow_succ_obj_eq T n (L.functor.obj a))).symm) ≫
        (eqToHom (congrArg T.obj
            (monadPow_succ_obj_eq T n (L.functor.obj a))) ≫
          T.μ.app ((monadPow T n).obj (L.functor.obj a))) := by
    have hA :
        (s L n).app a ≫
          (barFace (T := T) (R := RightModule.regular T) (L := L) n
              (0 : Fin (n + 2))).app a =
        (s L n).app a ≫
          (eqToHom (congrArg T.obj
              (monadPow_succ_obj_eq T n (L.functor.obj a))) ≫
            T.μ.app ((monadPow T n).obj (L.functor.obj a))) :=
      congrArg ((s L n).app a ≫ ·) hFaceEq
    have hB :
        (s L n).app a ≫
            (eqToHom (congrArg T.obj
                (monadPow_succ_obj_eq T n (L.functor.obj a))) ≫
              T.μ.app ((monadPow T n).obj (L.functor.obj a))) =
        (T.η.app (T.obj ((monadPow T n).obj (L.functor.obj a))) ≫
          eqToHom (congrArg T.obj
              (monadPow_succ_obj_eq T n (L.functor.obj a))).symm) ≫
          (eqToHom (congrArg T.obj
              (monadPow_succ_obj_eq T n (L.functor.obj a))) ≫
            T.μ.app ((monadPow T n).obj (L.functor.obj a))) :=
      congrArg (· ≫ (eqToHom (congrArg T.obj
          (monadPow_succ_obj_eq T n (L.functor.obj a))) ≫
        T.μ.app ((monadPow T n).obj (L.functor.obj a)))) hs
    exact hA.trans hB
  have hStep1 : (T.η.app (T.obj ((monadPow T n).obj (L.functor.obj a))) ≫
        eqToHom (congrArg T.obj (monadPow_succ_obj_eq T n (L.functor.obj a))).symm) ≫
        (eqToHom (congrArg T.obj (monadPow_succ_obj_eq T n (L.functor.obj a))) ≫
          T.μ.app ((monadPow T n).obj (L.functor.obj a))) =
      T.η.app (T.obj ((monadPow T n).obj (L.functor.obj a))) ≫
        (eqToHom (congrArg T.obj (monadPow_succ_obj_eq T n (L.functor.obj a))).symm ≫
          (eqToHom (congrArg T.obj (monadPow_succ_obj_eq T n (L.functor.obj a))) ≫
            T.μ.app ((monadPow T n).obj (L.functor.obj a)))) :=
      Category.assoc _ _ _
  have hStep2 : T.η.app (T.obj ((monadPow T n).obj (L.functor.obj a))) ≫
      (eqToHom (congrArg T.obj (monadPow_succ_obj_eq T n (L.functor.obj a))).symm ≫
        (eqToHom (congrArg T.obj (monadPow_succ_obj_eq T n (L.functor.obj a))) ≫
          T.μ.app ((monadPow T n).obj (L.functor.obj a)))) =
    T.η.app (T.obj ((monadPow T n).obj (L.functor.obj a))) ≫
      ((eqToHom (congrArg T.obj (monadPow_succ_obj_eq T n (L.functor.obj a))).symm ≫
        eqToHom (congrArg T.obj (monadPow_succ_obj_eq T n (L.functor.obj a))) ) ≫
        T.μ.app ((monadPow T n).obj (L.functor.obj a))) := by
    rw [Category.assoc (eqToHom (congrArg T.obj (monadPow_succ_obj_eq T n (L.functor.obj a))).symm)
      (eqToHom (congrArg T.obj (monadPow_succ_obj_eq T n (L.functor.obj a))))
      (T.μ.app ((monadPow T n).obj (L.functor.obj a)))]
  have hStep3 : T.η.app (T.obj ((monadPow T n).obj (L.functor.obj a))) ≫
      ((eqToHom (congrArg T.obj (monadPow_succ_obj_eq T n (L.functor.obj a))).symm ≫
        eqToHom (congrArg T.obj (monadPow_succ_obj_eq T n (L.functor.obj a))) ) ≫
        T.μ.app ((monadPow T n).obj (L.functor.obj a))) =
    T.η.app (T.obj ((monadPow T n).obj (L.functor.obj a))) ≫
      (𝟙 _ ≫ T.μ.app ((monadPow T n).obj (L.functor.obj a))) := by
    rw [eqToHom_symm_comp_eq]
  have hStep4 : T.η.app (T.obj ((monadPow T n).obj (L.functor.obj a))) ≫
      (𝟙 _ ≫ T.μ.app ((monadPow T n).obj (L.functor.obj a))) =
    T.η.app (T.obj ((monadPow T n).obj (L.functor.obj a))) ≫
      T.μ.app ((monadPow T n).obj (L.functor.obj a)) := by
    rw [Category.id_comp]
  exact hComp.trans (hStep1.trans (hStep2.trans (hStep3.trans (hStep4.trans
    (T.left_unit ((monadPow T n).obj (L.functor.obj a)))))))

/-! ### Auxiliary coherences for positive faces

The positive face `i.succ` is never the right endpoint `0`.  For
`i : Fin (n+2)` we have `(i.succ).val = i.val + 1`.  After unfolding
`s L n = η_{Bₙ} ≫ (barObj_obj_succ_eq)⁻¹` and using `T.η.naturality`,
the remaining comparison is `eq⁻¹ ≫ d_{i.succ} = T(d_i) ≫ eq⁻¹`,
i.e. forward `d_{i.succ} ≫ eq = eq ≫ T(d_i)`.  For

* `i = last` (left action) – `monadPow_obj_T_comm_naturality`,
* `i = 0` (right action vs last μ) – `mu_last_coherence`,
* `1 ≤ i ≤ n` (μ vs μ) – `mu_castSucc_coherence`,

all of which keep `eqToHom (monadPow_obj_T_comm)` explicit and use
`eqToHom_map` to move `T.map` past `eqToHom`.
-/

/--
Interior multiplication coherence: `μ` at `castSucc` commutes past the
`monadPow_obj_T_comm` transport up to `T.map`. Internal face-coherence input for
the positive-face contraction law with `1 ≤ i ≤ n`.
-/
theorem mu_castSucc_coherence {C : Type u₁} [Category.{v₁} C] {T : Monad C}
    (n : ℕ) (k : Fin n) (X : C) :
    muAtPos T (n + 1) k.castSucc X ≫ eqToHom (monadPow_obj_T_comm T n X) =
    eqToHom (monadPow_obj_T_comm T n (T.obj X)) ≫ T.map (muAtPos T n k X) := by
  induction n generalizing X with
  | zero => exact isEmptyElim k
  | succ n ih =>
    match k with
    | ⟨0, hk0⟩ =>
      change (monadPow T (n + 1)).map (T.μ.app X) ≫ eqToHom (monadPow_obj_T_comm T (n + 1) X) =
             eqToHom (monadPow_obj_T_comm T (n + 1) (T.obj X)) ≫
               T.map ((monadPow T n).map (T.μ.app X))
      have h_c : monadPow_obj_T_comm T (n + 1) X = monadPow_obj_T_comm T n (T.obj X) := rfl
      have h_cT : monadPow_obj_T_comm T (n + 1) (T.obj X) =
                  monadPow_obj_T_comm T n (T.obj (T.obj X)) := rfl
      rw [h_c, h_cT]
      have h_m : (monadPow T (n + 1)).map (T.μ.app X) =
                 (monadPow T n).map (T.map (T.μ.app X)) := rfl
      rw [h_m]
      exact monadPow_obj_T_comm_naturality T n (T.μ.app X)
    | ⟨k + 1, hk⟩ =>
      let k0 : Fin n := ⟨k, by omega⟩
      have h_cast_eq : (Fin.castSucc (⟨k + 1, hk⟩ : Fin (n + 1)) : Fin (n + 2)) =
                       (k0.castSucc).succ := by
        apply Fin.ext; simp [k0, Fin.castSucc]
      have h_mu_up : muAtPos T (n + 2) (Fin.castSucc (⟨k + 1, hk⟩ : Fin (n + 1))) X =
                     muAtPos T (n + 1) k0.castSucc (T.obj X) := by
        rw [h_cast_eq]; rfl
      have h_mu_low : muAtPos T (n + 1) (⟨k + 1, hk⟩ : Fin (n + 1)) X =
                      muAtPos T n k0 (T.obj X) := rfl
      rw [h_mu_up, h_mu_low]
      have h_c : monadPow_obj_T_comm T (n + 1) X = monadPow_obj_T_comm T n (T.obj X) := rfl
      have h_cT : monadPow_obj_T_comm T (n + 1) (T.obj X) =
                  monadPow_obj_T_comm T n (T.obj (T.obj X)) := rfl
      rw [h_c, h_cT]
      exact ih k0 (T.obj X)

/--
Right-end multiplication coherence: `μ` at `last` commutes past the successor
transport as `T.map` of transport followed by `μ`. Internal face-coherence input
for the `i = 0` positive-face case.
-/
theorem mu_last_coherence {C : Type u₁} [Category.{v₁} C] {T : Monad C}
    (n : ℕ) (X : C) :
    muAtPos T (n + 1) (Fin.last n) X ≫ eqToHom (monadPow_obj_T_comm T n X) =
    eqToHom (monadPow_obj_T_comm T n (T.obj X)) ≫
      T.map (eqToHom (monadPow_obj_T_comm T n X)) ≫ T.μ.app ((monadPow T n).obj X) := by
  induction n generalizing X with
  | zero =>
    have h_mu : muAtPos T 1 (Fin.last 0) X = T.μ.app X := rfl
    rw [h_mu]
    simp only [eqToHom_refl]
    simpa only [Category.comp_id, Category.id_comp, T.toFunctor.map_id, Category.assoc]
  | succ n ih =>
    have h_last_succ : (Fin.last (n + 1) : Fin (n + 2)) = (Fin.last n).succ := by
      apply Fin.ext; simp [Fin.last]
    have h_mu : muAtPos T (n + 2) (Fin.last (n + 1)) X =
                muAtPos T (n + 1) (Fin.last n) (T.obj X) := by
      rw [h_last_succ]; rfl
    have h_c : monadPow_obj_T_comm T (n + 1) X = monadPow_obj_T_comm T n (T.obj X) := rfl
    have h_cT : monadPow_obj_T_comm T (n + 1) (T.obj X) =
                monadPow_obj_T_comm T n (T.obj (T.obj X)) := rfl
    calc
      muAtPos T (n + 2) (Fin.last (n + 1)) X ≫ eqToHom (monadPow_obj_T_comm T (n + 1) X)
        = muAtPos T (n + 1) (Fin.last n) (T.obj X) ≫
            eqToHom (monadPow_obj_T_comm T n (T.obj X)) := by
          rw [h_mu, h_c]
      _ = eqToHom (monadPow_obj_T_comm T n (T.obj (T.obj X))) ≫
            T.map (eqToHom (monadPow_obj_T_comm T n (T.obj X))) ≫
              T.μ.app ((monadPow T n).obj (T.obj X)) := ih (T.obj X)
      _ = eqToHom (monadPow_obj_T_comm T n (T.obj (T.obj X))) ≫
            T.map (eqToHom (monadPow_obj_T_comm T n (T.obj X))) ≫
              T.μ.app ((monadPow T (n + 1)).obj X) := by rfl
      _ = eqToHom (monadPow_obj_T_comm T (n + 1) (T.obj X)) ≫
            T.map (eqToHom (monadPow_obj_T_comm T (n + 1) X)) ≫
              T.μ.app ((monadPow T (n + 1)).obj X) := by
          rw [h_c, h_cT]

/--
Regular-right positive-face contraction law.

For `n : ℕ` and `i : Fin (n+2)`, `i.succ : Fin (n+3)` is the positive
face at level `n+1`.  `s L (n+1)` inserts `η` at `B_{n+1}` then
`eqToHom (barObj_obj_succ_eq (n+1))⁻¹`.  Using `T.η.naturality`,
the comparison reduces to the transport-aware face coherence
`eq⁻¹ ≫ d_{i.succ} = T(d_i) ≫ eq⁻¹`, i.e. forward
`d_{i.succ} ≫ eq = eq ≫ T(d_i)`.

We split `i : Fin (n+2)` into endpoint vs interior:

* endpoint `i = last (n+1)` (`i.val = n+1`): `d_{last}` is the left
  action `T.map (M_n.map L.action)`.  Forward coherence is
  `monadPow_obj_T_comm_naturality T n (L.action)` together with
  `eqToHom_map`.

* interior `i.val ≤ n`: further into `i.val = 0` (right action) and
  `1 ≤ i.val ≤ n` (μ).  For `i=0`, `d_0 = rightActionPow n` and
  `d_1 = T.map (muAtPos (n+1) (last n))`; forward coherence is
  `mu_last_coherence`.  For `1 ≤ i ≤ n`, write `i = ⟨k+1⟩` with
  `k : Fin n`, `k' = k.succ : Fin (n+1)`, then
  `barMuAtPos n k = muAtPos n k.rev`, `barMuAtPos (n+1) k' = muAtPos (n+1) (k.rev).castSucc`,
  and `fin_rev_succ` gives the `castSucc` position.  Forward coherence
  is `mu_castSucc_coherence`.

In each case the forward equality `d_{i.succ} ≫ eq(b_n) = eq(b_{n+1}) ≫ T(d_i)`
is transformed to the inverse form `eq(b_{n+1})⁻¹ ≫ d_{i.succ} = T(d_i) ≫ eq(b_n)⁻¹`
via `eqToHom_comp_symm_eq` / `eqToHom_symm_comp_eq` and `Category.assoc`,
exactly as in `s_comp_barFace_zero`.  Finally `T.η.naturality` rewrites
`η_{n+1} ≫ T(d_i)` to `d_i ≫ η_n`, yielding the claimed
`s_{n+1} ≫ d_{i.succ} = d_i ≫ s_n`.
-/
theorem s_comp_barFace_succ (n : ℕ) (i : Fin (n + 2)) :
    s L (n + 1) ≫
        barFace (T := T) (R := RightModule.regular T) (L := L) (n + 1) i.succ =
      barFace (T := T) (R := RightModule.regular T) (L := L) n i ≫ s L n := by
  ext a
  let X := L.functor.obj a
  have h_eqHom_n : eqToHom (barObj_obj_succ_eq L n a) =
    T.map (eqToHom (monadPow_obj_T_comm T n X)) := by
    change eqToHom (congrArg T.obj (monadPow_obj_T_comm T n X)) = _
    exact (eqToHom_map (F := T.toFunctor) _).symm
  have h_eqHom_n1 : eqToHom (barObj_obj_succ_eq L (n + 1) a) =
    T.map (eqToHom (monadPow_obj_T_comm T (n + 1) X)) := by
    change eqToHom (congrArg T.obj (monadPow_obj_T_comm T (n + 1) X)) = _
    exact (eqToHom_map (F := T.toFunctor) _).symm
  have h_eqHom_n1_alt : eqToHom (barObj_obj_succ_eq L (n + 1) a) =
    T.map (eqToHom (monadPow_obj_T_comm T n (T.obj X))) := h_eqHom_n1
  -- single h_forward covering endpoint / zero / interior
  have h_forward : (barFace (T := T) (R := RightModule.regular T) (L := L) (n + 1) i.succ).app a ≫
      eqToHom (barObj_obj_succ_eq L n a) =
      eqToHom (barObj_obj_succ_eq L (n + 1) a) ≫
        T.map ((barFace (T := T) (R := RightModule.regular T) (L := L) n i).app a) := by
    by_cases h_last : i.val = n + 1
    · -- endpoint: i = last, left action
      have h_face_low : (barFace (T := T) (R := RightModule.regular T) (L := L) n i).app a =
        T.map ((monadPow T n).map (L.action.app a)) := by
        exact barFaceApp_of_val_last (T := T) (R := RightModule.regular T) (L := L) h_last
      have h_face_up :
          (barFace (T := T) (R := RightModule.regular T) (L := L)
            (n + 1) i.succ).app a =
        T.map ((monadPow T n).map (T.map (L.action.app a))) := by
        exact barFaceApp_of_val_last (T := T) (R := RightModule.regular T) (L := L)
          (by simp [h_last] : (i.succ).val = n + 2)
      have h1 : (barFace (T := T) (R := RightModule.regular T) (L := L) (n + 1) i.succ).app a ≫
          eqToHom (barObj_obj_succ_eq L n a) =
          T.map ((monadPow T n).map (T.map (L.action.app a))) ≫
            T.map (eqToHom (monadPow_obj_T_comm T n X)) := by
        have h1a : (barFace (T := T) (R := RightModule.regular T) (L := L) (n + 1) i.succ).app a ≫
            eqToHom (barObj_obj_succ_eq L n a) =
            T.map ((monadPow T n).map (T.map (L.action.app a))) ≫
              eqToHom (barObj_obj_succ_eq L n a) :=
          congrArg (· ≫ eqToHom (barObj_obj_succ_eq L n a)) h_face_up
        have h1b : T.map ((monadPow T n).map (T.map (L.action.app a))) ≫
            eqToHom (barObj_obj_succ_eq L n a) =
            T.map ((monadPow T n).map (T.map (L.action.app a))) ≫
              T.map (eqToHom (monadPow_obj_T_comm T n X)) :=
          congrArg (T.map ((monadPow T n).map (T.map (L.action.app a))) ≫ ·) h_eqHom_n
        exact h1a.trans h1b
      have h2 : T.map ((monadPow T n).map (T.map (L.action.app a))) ≫
          T.map (eqToHom (monadPow_obj_T_comm T n X)) =
          T.map ((monadPow T n).map (T.map (L.action.app a)) ≫
            eqToHom (monadPow_obj_T_comm T n X)) :=
        (T.toFunctor.map_comp _ _).symm
      have h3 : T.map ((monadPow T n).map (T.map (L.action.app a)) ≫
          eqToHom (monadPow_obj_T_comm T n X)) =
          T.map (eqToHom (monadPow_obj_T_comm T n (T.obj X)) ≫
            T.map ((monadPow T n).map (L.action.app a))) :=
        congrArg T.map (monadPow_obj_T_comm_naturality T n (L.action.app a))
      have h4 : T.map (eqToHom (monadPow_obj_T_comm T n (T.obj X)) ≫
          T.map ((monadPow T n).map (L.action.app a))) =
          T.map (eqToHom (monadPow_obj_T_comm T n (T.obj X))) ≫
            T.map (T.map ((monadPow T n).map (L.action.app a))) :=
        T.toFunctor.map_comp _ _
      have h5 : T.map (eqToHom (monadPow_obj_T_comm T n (T.obj X))) ≫
          T.map (T.map ((monadPow T n).map (L.action.app a))) =
          eqToHom (barObj_obj_succ_eq L (n + 1) a) ≫
            T.map (T.map ((monadPow T n).map (L.action.app a))) :=
        congrArg (· ≫ T.map (T.map ((monadPow T n).map (L.action.app a)))) h_eqHom_n1_alt.symm
      have h6 : eqToHom (barObj_obj_succ_eq L (n + 1) a) ≫
          T.map (T.map ((monadPow T n).map (L.action.app a))) =
          eqToHom (barObj_obj_succ_eq L (n + 1) a) ≫
            T.map ((barFace (T := T) (R := RightModule.regular T) (L := L) n i).app a) := by
        have h_eq : T.map (T.map ((monadPow T n).map (L.action.app a))) =
            T.map ((barFace (T := T) (R := RightModule.regular T) (L := L) n i).app a) :=
          congrArg T.map h_face_low.symm
        exact congrArg (eqToHom (barObj_obj_succ_eq L (n + 1) a) ≫ ·) h_eq
      exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6))))
    · have h_le : i.val ≤ n := by omega
      by_cases h_zero : i.val = 0
      · -- i = 0 : rightActionPow vs last μ, derive i = 0 via Fin.ext
        have hi_fin : i = (0 : Fin (n + 2)) := by
          apply Fin.ext
          exact h_zero
        have h_face_low_zero : (barFace (T := T) (R := RightModule.regular T) (L := L) n i).app a =
          rightActionPow T (RightModule.regular T) n X := by
          exact barFaceApp_of_val_zero (T := T) (R := RightModule.regular T) (L := L) h_zero
        have h_succ_val : (i.succ).val = 1 := by
          have h1 : (i.succ).val = (0 : Fin (n + 2)).succ.val :=
            congrArg Fin.val (congrArg Fin.succ hi_fin)
          have h2 : (0 : Fin (n + 2)).succ.val = 1 := rfl
          exact h1.trans h2
        have h_face_up_last :
            (barFace (T := T) (R := RightModule.regular T) (L := L)
              (n + 1) i.succ).app a =
          T.map (muAtPos T (n + 1) (Fin.last n) X) := by
          have h_eq :
              (barFaceApp (T := T) (R := RightModule.regular T) (L := L)
                (n + 1) i.succ a) =
            T.map (barMuAtPos T (n + 1) ⟨0, by omega⟩ X) := by
            exact barFaceApp_of_middle (T := T) (R := RightModule.regular T) (L := L) (n := n + 1)
              (k := ⟨0, by omega⟩) h_succ_val
          have h_barMu : barMuAtPos T (n + 1) ⟨0, by omega⟩ X =
            muAtPos T (n + 1) (Fin.last n) X := by
            simp only [barMuAtPos]
            have : (⟨0, by omega⟩ : Fin (n + 1)).rev = Fin.last n := by
              apply Fin.ext; simp [Fin.rev, Fin.last]
            exact congrArg (fun f => muAtPos T (n + 1) f X) this
          have h_rfl :
              (barFace (T := T) (R := RightModule.regular T) (L := L)
                (n + 1) i.succ).app a =
              barFaceApp (T := T) (R := RightModule.regular T) (L := L)
                (n + 1) i.succ a := rfl
          have h_step1 :
              barFaceApp (T := T) (R := RightModule.regular T) (L := L)
                (n + 1) i.succ a =
              T.map (barMuAtPos T (n + 1) ⟨0, by omega⟩ X) := h_eq
          have h_step2 : T.map (barMuAtPos T (n + 1) ⟨0, by omega⟩ X) =
              T.map (muAtPos T (n + 1) (Fin.last n) X) := congrArg T.map h_barMu
          exact h_rfl.trans (h_step1.trans h_step2)
        have h_right_eq : rightActionPow T (RightModule.regular T) n X =
          eqToHom (barObj_obj_succ_eq L n a) ≫ T.μ.app ((monadPow T n).obj X) := by
          have h_pow : rightActionPow T (RightModule.regular T) n X =
              (RightModule.regular T).functor.map
                  (eqToHom (monadPow_succ_obj_eq T n X)) ≫
                  (RightModule.regular T).action.app ((monadPow T n).obj X) :=
            rightActionPow_eq T (RightModule.regular T) n X
          have h_pow_rfl : (RightModule.regular T).functor.map
                  (eqToHom (monadPow_succ_obj_eq T n X)) ≫
                  (RightModule.regular T).action.app ((monadPow T n).obj X) =
              T.map (eqToHom (monadPow_succ_obj_eq T n X)) ≫ T.μ.app ((monadPow T n).obj X) := rfl
          have h_map_eq :
              T.map (eqToHom (monadPow_succ_obj_eq T n X)) ≫
                T.μ.app ((monadPow T n).obj X) =
              eqToHom (congrArg T.obj (monadPow_succ_obj_eq T n X)) ≫
                  T.μ.app ((monadPow T n).obj X) :=
            congrArg (· ≫ T.μ.app ((monadPow T n).obj X)) (eqToHom_map (F := T.toFunctor) _)
          have h_final_rfl : eqToHom (congrArg T.obj (monadPow_succ_obj_eq T n X)) ≫
                  T.μ.app ((monadPow T n).obj X) =
              eqToHom (barObj_obj_succ_eq L n a) ≫ T.μ.app ((monadPow T n).obj X) := rfl
          exact h_pow.trans (h_pow_rfl.trans (h_map_eq.trans h_final_rfl))
        have h1 : (barFace (T := T) (R := RightModule.regular T) (L := L) (n + 1) i.succ).app a ≫
            eqToHom (barObj_obj_succ_eq L n a) =
            T.map (muAtPos T (n + 1) (Fin.last n) X) ≫
              eqToHom (barObj_obj_succ_eq L n a) :=
          congrArg (· ≫ eqToHom (barObj_obj_succ_eq L n a)) h_face_up_last
        have h2 : T.map (muAtPos T (n + 1) (Fin.last n) X) ≫
            eqToHom (barObj_obj_succ_eq L n a) =
            T.map (muAtPos T (n + 1) (Fin.last n) X) ≫
              T.map (eqToHom (monadPow_obj_T_comm T n X)) :=
          congrArg (T.map (muAtPos T (n + 1) (Fin.last n) X) ≫ ·) h_eqHom_n
        have h3 : T.map (muAtPos T (n + 1) (Fin.last n) X) ≫
            T.map (eqToHom (monadPow_obj_T_comm T n X)) =
            T.map (muAtPos T (n + 1) (Fin.last n) X ≫
              eqToHom (monadPow_obj_T_comm T n X)) :=
          (T.toFunctor.map_comp _ _).symm
        have h4 : T.map (muAtPos T (n + 1) (Fin.last n) X ≫
            eqToHom (monadPow_obj_T_comm T n X)) =
            T.map (eqToHom (monadPow_obj_T_comm T n (T.obj X)) ≫
              T.map (eqToHom (monadPow_obj_T_comm T n X)) ≫
                T.μ.app ((monadPow T n).obj X)) :=
          congrArg T.map (mu_last_coherence n X)
        have h5 : T.map (eqToHom (monadPow_obj_T_comm T n (T.obj X)) ≫
            T.map (eqToHom (monadPow_obj_T_comm T n X)) ≫
              T.μ.app ((monadPow T n).obj X)) =
            T.map (eqToHom (monadPow_obj_T_comm T n (T.obj X))) ≫
              T.map (T.map (eqToHom (monadPow_obj_T_comm T n X))) ≫
                T.map (T.μ.app ((monadPow T n).obj X)) := by
          have h_comp1 : T.map (eqToHom (monadPow_obj_T_comm T n (T.obj X)) ≫
              (T.map (eqToHom (monadPow_obj_T_comm T n X)) ≫
                T.μ.app ((monadPow T n).obj X))) =
              T.map (eqToHom (monadPow_obj_T_comm T n (T.obj X))) ≫
                T.map (T.map (eqToHom (monadPow_obj_T_comm T n X)) ≫
                  T.μ.app ((monadPow T n).obj X)) :=
            T.toFunctor.map_comp _ _
          have h_comp2 : T.map (T.map (eqToHom (monadPow_obj_T_comm T n X)) ≫
              T.μ.app ((monadPow T n).obj X)) =
              T.map (T.map (eqToHom (monadPow_obj_T_comm T n X))) ≫
                T.map (T.μ.app ((monadPow T n).obj X)) :=
            T.toFunctor.map_comp _ _
          have h_mid : T.map (eqToHom (monadPow_obj_T_comm T n (T.obj X))) ≫
              T.map (T.map (eqToHom (monadPow_obj_T_comm T n X)) ≫
                T.μ.app ((monadPow T n).obj X)) =
              T.map (eqToHom (monadPow_obj_T_comm T n (T.obj X))) ≫
                (T.map (T.map (eqToHom (monadPow_obj_T_comm T n X))) ≫
                  T.map (T.μ.app ((monadPow T n).obj X))) :=
            congrArg (T.map (eqToHom (monadPow_obj_T_comm T n (T.obj X))) ≫ ·) h_comp2
          exact h_comp1.trans h_mid
        have h6 : T.map (eqToHom (monadPow_obj_T_comm T n (T.obj X))) ≫
            T.map (T.map (eqToHom (monadPow_obj_T_comm T n X))) ≫
              T.map (T.μ.app ((monadPow T n).obj X)) =
            eqToHom (barObj_obj_succ_eq L (n + 1) a) ≫
              T.map (eqToHom (barObj_obj_succ_eq L n a)) ≫
                T.map (T.μ.app ((monadPow T n).obj X)) := by
          have ha : T.map (eqToHom (monadPow_obj_T_comm T n (T.obj X))) =
              eqToHom (barObj_obj_succ_eq L (n + 1) a) := h_eqHom_n1_alt.symm
          have hb : T.map (eqToHom (monadPow_obj_T_comm T n X)) =
              eqToHom (barObj_obj_succ_eq L n a) := h_eqHom_n.symm
          have hc : T.map (T.map (eqToHom (monadPow_obj_T_comm T n X))) =
              T.map (eqToHom (barObj_obj_succ_eq L n a)) := congrArg T.map hb
          have h6a : T.map (eqToHom (monadPow_obj_T_comm T n (T.obj X))) ≫
              T.map (T.map (eqToHom (monadPow_obj_T_comm T n X))) ≫
                T.map (T.μ.app ((monadPow T n).obj X)) =
              eqToHom (barObj_obj_succ_eq L (n + 1) a) ≫
                T.map (T.map (eqToHom (monadPow_obj_T_comm T n X))) ≫
                  T.map (T.μ.app ((monadPow T n).obj X)) :=
            congrArg (· ≫ T.map (T.map (eqToHom (monadPow_obj_T_comm T n X))) ≫
              T.map (T.μ.app ((monadPow T n).obj X))) ha
          have h6b : eqToHom (barObj_obj_succ_eq L (n + 1) a) ≫
                T.map (T.map (eqToHom (monadPow_obj_T_comm T n X))) ≫
                  T.map (T.μ.app ((monadPow T n).obj X)) =
              eqToHom (barObj_obj_succ_eq L (n + 1) a) ≫
                T.map (eqToHom (barObj_obj_succ_eq L n a)) ≫
                  T.map (T.μ.app ((monadPow T n).obj X)) :=
            congrArg (eqToHom (barObj_obj_succ_eq L (n + 1) a) ≫ · ≫
              T.map (T.μ.app ((monadPow T n).obj X))) hc
          exact h6a.trans h6b
        have h7 : eqToHom (barObj_obj_succ_eq L (n + 1) a) ≫
            T.map (eqToHom (barObj_obj_succ_eq L n a)) ≫
              T.map (T.μ.app ((monadPow T n).obj X)) =
            eqToHom (barObj_obj_succ_eq L (n + 1) a) ≫
              T.map (eqToHom (barObj_obj_succ_eq L n a) ≫
                T.μ.app ((monadPow T n).obj X)) := by
          have h_assoc : eqToHom (barObj_obj_succ_eq L (n + 1) a) ≫
              T.map (eqToHom (barObj_obj_succ_eq L n a)) ≫
                T.map (T.μ.app ((monadPow T n).obj X)) =
              eqToHom (barObj_obj_succ_eq L (n + 1) a) ≫
                (T.map (eqToHom (barObj_obj_succ_eq L n a)) ≫
                  T.map (T.μ.app ((monadPow T n).obj X))) := rfl
          have h_map : T.map (eqToHom (barObj_obj_succ_eq L n a)) ≫
              T.map (T.μ.app ((monadPow T n).obj X)) =
              T.map (eqToHom (barObj_obj_succ_eq L n a) ≫
                T.μ.app ((monadPow T n).obj X)) :=
            (T.toFunctor.map_comp _ _).symm
          exact h_assoc.trans (congrArg (eqToHom (barObj_obj_succ_eq L (n + 1) a) ≫ ·) h_map)
        have h8 : eqToHom (barObj_obj_succ_eq L (n + 1) a) ≫
            T.map (eqToHom (barObj_obj_succ_eq L n a) ≫
              T.μ.app ((monadPow T n).obj X)) =
            eqToHom (barObj_obj_succ_eq L (n + 1) a) ≫
              T.map ((barFace (T := T) (R := RightModule.regular T) (L := L) n i).app a) := by
          have h_inner_eq : eqToHom (barObj_obj_succ_eq L n a) ≫
              T.μ.app ((monadPow T n).obj X) =
              (barFace (T := T) (R := RightModule.regular T) (L := L) n i).app a := by
            have h1 : eqToHom (barObj_obj_succ_eq L n a) ≫
                T.μ.app ((monadPow T n).obj X) = rightActionPow T (RightModule.regular T) n X :=
              h_right_eq.symm
            have h2 : rightActionPow T (RightModule.regular T) n X =
                (barFace (T := T) (R := RightModule.regular T) (L := L) n i).app a :=
              h_face_low_zero.symm
            exact h1.trans h2
          exact congrArg (eqToHom (barObj_obj_succ_eq L (n + 1) a) ≫ ·)
            (congrArg T.map h_inner_eq)
        exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans h8))))))
      · -- 1 ≤ i.val ≤ n : μ vs μ, use h_mu_up_cast via substitution before calc
        let k : Fin n := ⟨i.val - 1, by omega⟩
        have hk_eq : i.val = k.val + 1 := by simp [k]; omega
        let k' : Fin (n + 1) := ⟨i.val, by omega⟩
        have hk'_eq : i.val = k'.val := rfl
        have hk'_succ : k' = k.succ := by
          apply Fin.ext; simp [k, k', Fin.succ]; omega
        have h_face_low_mid : (barFace (T := T) (R := RightModule.regular T) (L := L) n i).app a =
          T.map (barMuAtPos T n k X) := by
          exact barFaceApp_of_middle (T := T) (R := RightModule.regular T) (L := L) (k := k) hk_eq
        have h_succ_val_aux : (i.succ).val = i.val + 1 := by
          have h : (Fin.succ i : Fin (n + 3)).val = i.val + 1 := rfl
          exact h
        have h_succ_mid : (i.succ).val = k'.val + 1 := by
          calc (i.succ).val = i.val + 1 := h_succ_val_aux
               _ = k'.val + 1 := by rw [hk'_eq]
        have h_face_up_mid :
            (barFace (T := T) (R := RightModule.regular T) (L := L)
              (n + 1) i.succ).app a =
          T.map (barMuAtPos T (n + 1) k' X) := by
          exact barFaceApp_of_middle (T := T) (R := RightModule.regular T)
            (L := L) (k := k') h_succ_mid
        have h_barMu_low : barMuAtPos T n k X = muAtPos T n k.rev X := rfl
        have h_rev_succ : k'.rev = (k.rev).castSucc := by
          rw [hk'_succ]; exact fin_rev_succ k
        have h_barMu_up_cast : barMuAtPos T (n + 1) k' X =
            muAtPos T (n + 1) (k.rev).castSucc X := by
          calc
            barMuAtPos T (n + 1) k' X = muAtPos T (n + 1) k'.rev X := rfl
            _ = muAtPos T (n + 1) (k.rev).castSucc X :=
              congrArg (fun f => muAtPos T (n + 1) f X) h_rev_succ
        have h_face_up_mid_cast :
            (barFace (T := T) (R := RightModule.regular T) (L := L)
              (n + 1) i.succ).app a =
            T.map (muAtPos T (n + 1) (k.rev).castSucc X) :=
          h_face_up_mid.trans (congrArg T.map h_barMu_up_cast)
        have h1 : (barFace (T := T) (R := RightModule.regular T) (L := L) (n + 1) i.succ).app a ≫
            eqToHom (barObj_obj_succ_eq L n a) =
            T.map (muAtPos T (n + 1) (k.rev).castSucc X) ≫
              eqToHom (barObj_obj_succ_eq L n a) :=
          congrArg (· ≫ eqToHom (barObj_obj_succ_eq L n a)) h_face_up_mid_cast
        have h2 : T.map (muAtPos T (n + 1) (k.rev).castSucc X) ≫
            eqToHom (barObj_obj_succ_eq L n a) =
            T.map (muAtPos T (n + 1) (k.rev).castSucc X) ≫
              T.map (eqToHom (monadPow_obj_T_comm T n X)) :=
          congrArg (T.map (muAtPos T (n + 1) (k.rev).castSucc X) ≫ ·) h_eqHom_n
        have h3 : T.map (muAtPos T (n + 1) (k.rev).castSucc X) ≫
            T.map (eqToHom (monadPow_obj_T_comm T n X)) =
            T.map (muAtPos T (n + 1) (k.rev).castSucc X ≫
              eqToHom (monadPow_obj_T_comm T n X)) :=
          (T.toFunctor.map_comp _ _).symm
        have h4 : T.map (muAtPos T (n + 1) (k.rev).castSucc X ≫
            eqToHom (monadPow_obj_T_comm T n X)) =
            T.map (eqToHom (monadPow_obj_T_comm T n (T.obj X)) ≫
              T.map (muAtPos T n k.rev X)) :=
          congrArg T.map (mu_castSucc_coherence n k.rev X)
        have h5 : T.map (eqToHom (monadPow_obj_T_comm T n (T.obj X)) ≫
            T.map (muAtPos T n k.rev X)) =
            T.map (eqToHom (monadPow_obj_T_comm T n (T.obj X))) ≫
              T.map (T.map (muAtPos T n k.rev X)) :=
          T.toFunctor.map_comp _ _
        have h6 : T.map (eqToHom (monadPow_obj_T_comm T n (T.obj X))) ≫
            T.map (T.map (muAtPos T n k.rev X)) =
            eqToHom (barObj_obj_succ_eq L (n + 1) a) ≫
              T.map (T.map (muAtPos T n k.rev X)) :=
          congrArg (· ≫ T.map (T.map (muAtPos T n k.rev X))) h_eqHom_n1_alt.symm
        have h7 : eqToHom (barObj_obj_succ_eq L (n + 1) a) ≫
            T.map (T.map (muAtPos T n k.rev X)) =
            eqToHom (barObj_obj_succ_eq L (n + 1) a) ≫
              T.map (T.map (barMuAtPos T n k X)) := by
          have h_mu_map : T.map (muAtPos T n k.rev X) = T.map (barMuAtPos T n k X) :=
            congrArg T.map h_barMu_low.symm
          have h_outer : T.map (T.map (muAtPos T n k.rev X)) =
              T.map (T.map (barMuAtPos T n k X)) := congrArg T.map h_mu_map
          exact congrArg (eqToHom (barObj_obj_succ_eq L (n + 1) a) ≫ ·) h_outer
        have h8 : eqToHom (barObj_obj_succ_eq L (n + 1) a) ≫
            T.map (T.map (barMuAtPos T n k X)) =
            eqToHom (barObj_obj_succ_eq L (n + 1) a) ≫
              T.map ((barFace (T := T) (R := RightModule.regular T) (L := L)
                n i).app a) := by
          have h_eq : T.map (barMuAtPos T n k X) =
              (barFace (T := T) (R := RightModule.regular T) (L := L)
                n i).app a := h_face_low_mid.symm
          have h_congr : T.map (T.map (barMuAtPos T n k X)) =
              T.map ((barFace (T := T) (R := RightModule.regular T) (L := L)
                n i).app a) :=
            congrArg T.map h_eq
          exact congrArg (eqToHom (barObj_obj_succ_eq L (n + 1) a) ≫ ·) h_congr
        exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans h8))))))
  -- prove inverse square once by cancelling iso on right
  have h_inner : eqToHom (barObj_obj_succ_eq L (n + 1) a).symm ≫
      (barFace (T := T) (R := RightModule.regular T) (L := L) (n + 1) i.succ).app a =
      T.map ((barFace (T := T) (R := RightModule.regular T) (L := L) n i).app a) ≫
        eqToHom (barObj_obj_succ_eq L n a).symm := by
    rw [← cancel_mono (eqToHom (barObj_obj_succ_eq L n a))]
    calc
      (eqToHom (barObj_obj_succ_eq L (n + 1) a).symm ≫
          (barFace (T := T) (R := RightModule.regular T) (L := L) (n + 1) i.succ).app a) ≫
          eqToHom (barObj_obj_succ_eq L n a)
        = eqToHom (barObj_obj_succ_eq L (n + 1) a).symm ≫
            ((barFace (T := T) (R := RightModule.regular T) (L := L) (n + 1) i.succ).app a ≫
              eqToHom (barObj_obj_succ_eq L n a)) :=
        Category.assoc _ _ _
      _ = eqToHom (barObj_obj_succ_eq L (n + 1) a).symm ≫
            (eqToHom (barObj_obj_succ_eq L (n + 1) a) ≫
              T.map ((barFace (T := T) (R := RightModule.regular T) (L := L) n i).app a)) :=
        congrArg (eqToHom (barObj_obj_succ_eq L (n + 1) a).symm ≫ ·) h_forward
      _ = (eqToHom (barObj_obj_succ_eq L (n + 1) a).symm ≫
            eqToHom (barObj_obj_succ_eq L (n + 1) a)) ≫
              T.map ((barFace (T := T) (R := RightModule.regular T) (L := L) n i).app a) :=
        (Category.assoc _ _ _).symm
      _ = 𝟙 _ ≫ T.map ((barFace (T := T) (R := RightModule.regular T) (L := L) n i).app a) :=
        congrArg (· ≫ T.map ((barFace (T := T) (R := RightModule.regular T) (L := L) n i).app a))
          (eqToHom_symm_comp_eq (barObj_obj_succ_eq L (n + 1) a))
      _ = T.map ((barFace (T := T) (R := RightModule.regular T) (L := L) n i).app a) :=
        Category.id_comp _
      _ = T.map ((barFace (T := T) (R := RightModule.regular T) (L := L) n i).app a) ≫ 𝟙 _ :=
        (Category.comp_id _).symm
      _ = T.map ((barFace (T := T) (R := RightModule.regular T) (L := L) n i).app a) ≫
            (eqToHom (barObj_obj_succ_eq L n a).symm ≫
              eqToHom (barObj_obj_succ_eq L n a)) :=
        congrArg (T.map ((barFace (T := T) (R := RightModule.regular T) (L := L) n i).app a) ≫ ·)
          (eqToHom_symm_comp_eq (barObj_obj_succ_eq L n a)).symm
      _ = (T.map ((barFace (T := T) (R := RightModule.regular T) (L := L) n i).app a) ≫
            eqToHom (barObj_obj_succ_eq L n a).symm) ≫
              eqToHom (barObj_obj_succ_eq L n a) :=
        (Category.assoc _ _ _).symm
  -- finish once, outside case split, by unfolding only component of composition
  -- and rewriting with public s_app lemma at degrees n+1 and n
  have h_comp_left : (s L (n + 1) ≫
      barFace (T := T) (R := RightModule.regular T) (L := L)
        (n + 1) i.succ).app a =
      (s L (n + 1)).app a ≫
        (barFace (T := T) (R := RightModule.regular T) (L := L)
          (n + 1) i.succ).app a := rfl
  have h_comp_right :
      (barFace (T := T) (R := RightModule.regular T) (L := L)
        n i ≫ s L n).app a =
      (barFace (T := T) (R := RightModule.regular T) (L := L)
        n i).app a ≫
        (s L n).app a := rfl
  calc
    (s L (n + 1) ≫
        barFace (T := T) (R := RightModule.regular T) (L := L)
          (n + 1) i.succ).app a
      = (s L (n + 1)).app a ≫
          (barFace (T := T) (R := RightModule.regular T) (L := L)
            (n + 1) i.succ).app a := h_comp_left
    _ = (T.η.app ((barObj T (RightModule.regular T) L (n + 1)).obj a) ≫
          eqToHom (barObj_obj_succ_eq L (n + 1) a).symm) ≫
            (barFace (T := T) (R := RightModule.regular T) (L := L)
              (n + 1) i.succ).app a := by
          have hs : (s L (n + 1)).app a =
              T.η.app ((barObj T (RightModule.regular T) L (n + 1)).obj a) ≫
                eqToHom (barObj_obj_succ_eq L (n + 1) a).symm := rfl
          exact congrArg
            (· ≫ (barFace (T := T) (R := RightModule.regular T) (L := L)
              (n + 1) i.succ).app a) hs
    _ = T.η.app ((barObj T (RightModule.regular T) L (n + 1)).obj a) ≫
          (eqToHom (barObj_obj_succ_eq L (n + 1) a).symm ≫
            (barFace (T := T) (R := RightModule.regular T) (L := L)
              (n + 1) i.succ).app a) :=
        Category.assoc _ _ _
    _ = T.η.app ((barObj T (RightModule.regular T) L (n + 1)).obj a) ≫
          (T.map ((barFace (T := T) (R := RightModule.regular T) (L := L) n i).app a) ≫
            eqToHom (barObj_obj_succ_eq L n a).symm) :=
        congrArg (T.η.app ((barObj T (RightModule.regular T) L (n + 1)).obj a) ≫ ·) h_inner
    _ = (T.η.app ((barObj T (RightModule.regular T) L (n + 1)).obj a) ≫
          T.map ((barFace (T := T) (R := RightModule.regular T) (L := L) n i).app a)) ≫
            eqToHom (barObj_obj_succ_eq L n a).symm :=
        (Category.assoc _ _ _).symm
    _ = ((barFace (T := T) (R := RightModule.regular T) (L := L) n i).app a ≫
          T.η.app ((barObj T (RightModule.regular T) L n).obj a)) ≫
            eqToHom (barObj_obj_succ_eq L n a).symm := by
          have h_eta :=
            T.η.naturality
              ((barFace (T := T) (R := RightModule.regular T) (L := L) n i).app a)
          change (barFace (T := T) (R := RightModule.regular T) (L := L) n i).app a ≫
              T.η.app ((barObj T (RightModule.regular T) L n).obj a) =
              T.η.app ((barObj T (RightModule.regular T) L (n + 1)).obj a) ≫
                T.map ((barFace (T := T) (R := RightModule.regular T) (L := L) n i).app a) at h_eta
          have h_step : T.η.app ((barObj T (RightModule.regular T) L (n + 1)).obj a) ≫
              T.map ((barFace (T := T) (R := RightModule.regular T) (L := L) n i).app a) =
              (barFace (T := T) (R := RightModule.regular T) (L := L) n i).app a ≫
                T.η.app ((barObj T (RightModule.regular T) L n).obj a) := h_eta.symm
          exact congrArg (· ≫ eqToHom (barObj_obj_succ_eq L n a).symm) h_step
    _ = (barFace (T := T) (R := RightModule.regular T) (L := L) n i).app a ≫
          (T.η.app ((barObj T (RightModule.regular T) L n).obj a) ≫
            eqToHom (barObj_obj_succ_eq L n a).symm) :=
        Category.assoc _ _ _
    _ = (barFace (T := T) (R := RightModule.regular T) (L := L) n i).app a ≫
          (s L n).app a := by
          have hs : (s L n).app a =
              T.η.app ((barObj T (RightModule.regular T) L n).obj a) ≫
                eqToHom (barObj_obj_succ_eq L n a).symm := rfl
          exact congrArg
            ((barFace (T := T) (R := RightModule.regular T) (L := L) n i).app a ≫ ·) hs.symm
    _ = (barFace (T := T) (R := RightModule.regular T) (L := L) n i ≫ s L n).app a :=
          h_comp_right.symm

/-! ### Left-handed degeneracy compatibility
`s` inserts the outer unit and `σ i` inserts `η` at raw `i.rev`
(`barData_σ_app`); `fin_rev_succ` reduces it to the `η` analogue of
`mu_castSucc_coherence` below. -/

theorem eta_castSucc_comm_coherence {C : Type u₁}
    [Category.{v₁} C] {T : Monad C} (n : ℕ) (k : Fin (n + 1))
    (X : C) :
    etaAtPos T (n + 1) k.castSucc X ≫
      eqToHom (monadPow_obj_T_comm T n (T.obj X)) =
    eqToHom (monadPow_obj_T_comm T n X) ≫
      T.map (etaAtPos T n k X) := by
  induction n generalizing X with
  | zero =>
    have hk_eq : k = (⟨0, by omega⟩ : Fin 1) := by
      apply Fin.ext
      have h := k.isLt
      omega
    have hcast :
        (Fin.castSucc (⟨0, by omega⟩ : Fin 1) : Fin 2) =
        (⟨0, by omega⟩ : Fin 2) := by
      apply Fin.ext
      simp
    rw [hk_eq, hcast]
    have heta_up : etaAtPos T 1 (⟨0, by omega⟩ : Fin 2) X =
        T.map (T.η.app X) := rfl
    have heta_low : etaAtPos T 0 (⟨0, by omega⟩ : Fin 1) X =
        T.η.app X := rfl
    rw [heta_up, heta_low]
    simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  | succ n ih =>
    match k with
    | ⟨0, hk0⟩ =>
      have hcast0 :
          (Fin.castSucc (⟨0, hk0⟩ : Fin (n + 2)) : Fin (n + 3)) =
          (⟨0, by omega⟩ : Fin (n + 3)) := by
        apply Fin.ext
        simp
      have heta_up : etaAtPos T (n + 2)
          (Fin.castSucc (⟨0, hk0⟩ : Fin (n + 2))) X =
          (monadPow T (n + 2)).map (T.η.app X) := by rw [hcast0]; exact rfl
      have heta_low : etaAtPos T (n + 1)
          (⟨0, hk0⟩ : Fin (n + 2)) X =
          (monadPow T (n + 1)).map (T.η.app X) := rfl
      have h_c : monadPow_obj_T_comm T (n + 1) X =
          monadPow_obj_T_comm T n (T.obj X) := rfl
      have h_cT : monadPow_obj_T_comm T (n + 1) (T.obj X) =
          monadPow_obj_T_comm T n (T.obj (T.obj X)) := rfl
      have h_m : (monadPow T (n + 2)).map (T.η.app X) =
          (monadPow T (n + 1)).map (T.map (T.η.app X)) := rfl
      rw [heta_up, heta_low, h_c, h_cT, h_m]
      exact monadPow_obj_T_comm_naturality T (n + 1) (T.η.app X)
    | ⟨k + 1, hk⟩ =>
      let k0 : Fin (n + 1) := ⟨k, by omega⟩
      have h_cast_eq :
          (Fin.castSucc (⟨k + 1, hk⟩ : Fin (n + 2)) :
            Fin (n + 3)) = (k0.castSucc).succ := by
        apply Fin.ext
        simp [k0, Fin.castSucc, Fin.succ]
      have h_eta_up : etaAtPos T (n + 2)
          (Fin.castSucc (⟨k + 1, hk⟩ : Fin (n + 2))) X =
          etaAtPos T (n + 1) k0.castSucc (T.obj X) := by
        rw [h_cast_eq]
        rfl
      have h_eta_low : etaAtPos T (n + 1)
          (⟨k + 1, hk⟩ : Fin (n + 2)) X =
          etaAtPos T n k0 (T.obj X) := rfl
      have h_c : monadPow_obj_T_comm T (n + 1) X =
          monadPow_obj_T_comm T n (T.obj X) := rfl
      have h_cT : monadPow_obj_T_comm T (n + 1) (T.obj X) =
          monadPow_obj_T_comm T n (T.obj (T.obj X)) := rfl
      rw [h_eta_up, h_eta_low, h_c, h_cT]
      exact ih k0 (T.obj X)

/-- Left-handed degeneracy law on `barData` through `Fin.succ`. -/
theorem s_comp_σ_succ_app_aux_barData (n : ℕ)
    (i : Fin (n + 1)) (a : A) :
    (s L n).app a ≫
      ((barData T (RightModule.regular T) L).σ i.succ).app a =
    ((barData T (RightModule.regular T) L).σ i).app a ≫
      (s L (n + 1)).app a := by
  have hσ_low := barData_σ_app T (RightModule.regular T) L
    (n := n) (i := i) (a := a)
  have hσ_up := barData_σ_app T (RightModule.regular T) L
    (n := n + 1) (i := i.succ) (a := a)
  have h_rev : (i.succ).rev = (i.rev).castSucc := fin_rev_succ i
  have h_low_eq :
      ((barData T (RightModule.regular T) L).σ i).app a =
      T.map (etaAtPos T n i.rev (L.functor.obj a)) := by
    rw [hσ_low, barEtaAtPos_rev]; exact rfl
  have h_up_eq :
      ((barData T (RightModule.regular T) L).σ i.succ).app a =
      T.map (etaAtPos T (n + 1) (i.rev).castSucc
        (L.functor.obj a)) := by
    rw [hσ_up, barEtaAtPos_rev, h_rev]; exact rfl
  have h_eqHom_n : eqToHom (barObj_obj_succ_eq L n a) =
      T.map (eqToHom (monadPow_obj_T_comm T n
        (L.functor.obj a))) := by
    change eqToHom (congrArg T.obj
      (monadPow_obj_T_comm T n _)) = _
    exact (eqToHom_map (F := T.toFunctor) _).symm
  have h_eqHom_n1 : eqToHom (barObj_obj_succ_eq L (n + 1) a) =
      T.map (eqToHom (monadPow_obj_T_comm T (n + 1)
        (L.functor.obj a))) := by
    change eqToHom (congrArg T.obj
      (monadPow_obj_T_comm T (n + 1) _)) = _
    exact (eqToHom_map (F := T.toFunctor) _).symm
  have h_eqHom_n1_alt : eqToHom (barObj_obj_succ_eq L (n + 1) a) =
      T.map (eqToHom (monadPow_obj_T_comm T n
        (T.obj (L.functor.obj a)))) := h_eqHom_n1
  have h_map := congrArg T.map
    (eta_castSucc_comm_coherence (T := T) n i.rev (L.functor.obj a))
  rw [T.toFunctor.map_comp, T.toFunctor.map_comp] at h_map
  have h_forward :
      T.map (etaAtPos T (n + 1) (i.rev).castSucc
          (L.functor.obj a)) ≫
        eqToHom (barObj_obj_succ_eq L (n + 1) a) =
      eqToHom (barObj_obj_succ_eq L n a) ≫
        T.map (T.map (etaAtPos T n i.rev
          (L.functor.obj a))) := by
    exact (congrArg (T.map (etaAtPos T (n + 1) (i.rev).castSucc
      (L.functor.obj a)) ≫ ·) h_eqHom_n1_alt).trans (h_map.trans
      (congrArg (· ≫ T.map (T.map (etaAtPos T n i.rev
        (L.functor.obj a)))) h_eqHom_n.symm))
  have h_inner : eqToHom (barObj_obj_succ_eq L n a).symm ≫
      T.map (etaAtPos T (n + 1) (i.rev).castSucc (L.functor.obj a)) =
      T.map (T.map (etaAtPos T n i.rev (L.functor.obj a))) ≫
        eqToHom (barObj_obj_succ_eq L (n + 1) a).symm :=
    (congrArg (eqToHom (barObj_obj_succ_eq L n a).symm ≫ ·)
      ((Category.comp_id _).symm.trans
        (congrArg (T.map (etaAtPos T (n + 1) (i.rev).castSucc
          (L.functor.obj a)) ≫ ·)
          (eqToHom_comp_symm_eq
            (barObj_obj_succ_eq L (n + 1) a)).symm))).trans
      ((congrArg (eqToHom (barObj_obj_succ_eq L n a).symm ≫ ·)
        ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ eqToHom (barObj_obj_succ_eq L (n + 1) a).symm)
            h_forward))).trans
        (((congrArg (eqToHom (barObj_obj_succ_eq L n a).symm ≫ ·)
          (Category.assoc _ _ _)).trans
          (Category.assoc _ _ _).symm).trans
          ((congrArg (· ≫ (T.map (T.map (etaAtPos T n i.rev
            (L.functor.obj a))) ≫ eqToHom (barObj_obj_succ_eq L
            (n + 1) a).symm))
            (eqToHom_symm_comp_eq
              (barObj_obj_succ_eq L n a))).trans
            (Category.id_comp _))))
  have h_eta := T.η.naturality
    (((barData T (RightModule.regular T) L).σ i).app a)
  change ((barData T (RightModule.regular T) L).σ i).app a ≫
      T.η.app ((barObj T (RightModule.regular T) L
        (n + 1)).obj a) =
      T.η.app ((barObj T (RightModule.regular T) L n).obj a) ≫
        T.map (((barData T (RightModule.regular T) L).σ i).app a)
    at h_eta
  have h_map_σ : T.map
      (((barData T (RightModule.regular T) L).σ i).app a) =
      T.map (T.map (etaAtPos T n i.rev
        (L.functor.obj a))) :=
    congrArg T.map h_low_eq
  have h_step : T.η.app
        ((barObj T (RightModule.regular T) L n).obj a) ≫
        T.map (T.map (etaAtPos T n i.rev
          (L.functor.obj a))) =
      ((barData T (RightModule.regular T) L).σ i).app a ≫
        T.η.app ((barObj T (RightModule.regular T) L
          (n + 1)).obj a) :=
    (congrArg (T.η.app ((barObj T (RightModule.regular T) L n).obj a) ≫ ·)
      h_map_σ).symm.trans h_eta.symm
  exact (((congrArg (· ≫ ((barData T (RightModule.regular T) L).σ i.succ).app a)
    (s_app L n a)).trans
    (congrArg ((T.η.app ((barObj T (RightModule.regular T) L n).obj a) ≫
      eqToHom (barObj_obj_succ_eq L n a).symm) ≫ ·) h_up_eq)).trans
    ((Category.assoc (T.η.app ((barObj T (RightModule.regular T) L n).obj a))
      (eqToHom (barObj_obj_succ_eq L n a).symm)
      (T.map (etaAtPos T (n + 1) (i.rev).castSucc
        (L.functor.obj a)))).trans
      (congrArg (T.η.app ((barObj T (RightModule.regular T) L n).obj a)
        ≫ ·) h_inner))).trans
    (((Category.assoc (T.η.app ((barObj T (RightModule.regular T) L n).obj a))
      (T.map (T.map (etaAtPos T n i.rev (L.functor.obj a))))
      (eqToHom (barObj_obj_succ_eq L (n + 1) a).symm)).symm.trans
      (congrArg (· ≫ eqToHom (barObj_obj_succ_eq L (n + 1) a).symm)
        h_step)).trans
      ((Category.assoc (((barData T (RightModule.regular T) L).σ i).app a)
        (T.η.app ((barObj T (RightModule.regular T) L (n + 1)).obj a))
        (eqToHom (barObj_obj_succ_eq L (n + 1) a).symm)).trans
        (congrArg (((barData T (RightModule.regular T) L).σ i).app a ≫ ·)
          (s_app L (n + 1) a).symm)))

/-- Left-handed degeneracy law on the augmented data. -/
theorem s_comp_σ_succ (n : ℕ) (i : Fin (n + 1)) :
    s L n ≫ (regularBalancedPairing L).toAugmented.left.σ i.succ =
    (regularBalancedPairing L).toAugmented.left.σ i ≫
      s L (n + 1) := by
  have h_up : (regularBalancedPairing L).toAugmented.left.σ i.succ =
      (barData T (RightModule.regular T) L).σ i.succ := rfl
  have h_low : (regularBalancedPairing L).toAugmented.left.σ i =
      (barData T (RightModule.regular T) L).σ i := rfl
  rw [h_up, h_low]
  ext a : 2
  exact s_comp_σ_succ_app_aux_barData L n i a

/-- Data-level left extra degeneracy for the regular-right bar. -/
noncomputable def extraDegeneracy :
    SimplicialObject.Data.Augmented.ExtraDegeneracy
      (regularBalancedPairing L).toAugmented where
  s' := s' L
  s := s L
  s'_comp_ε := by
    have h : (regularBalancedPairing L).toAugmented.hom.app 0 =
      regularPairing L := BalancedPairing.toAugmented_hom_app_zero _
    rw [h]
    exact s'_comp_regularPairing L
  s₀_comp_δ₁ := by
    have hδ : (regularBalancedPairing L).toAugmented.left.δ (1 : Fin 2) =
        barFace (T := T) (R := RightModule.regular T) (L := L) 0
          (1 : Fin 2) := rfl
    have hhom : (regularBalancedPairing L).toAugmented.hom.app 0 =
      regularPairing L := BalancedPairing.toAugmented_hom_app_zero _
    rw [hδ, hhom]
    exact s_zero_comp_barFace_last L
  s_comp_δ₀ := by
    intro n
    have hδ : (regularBalancedPairing L).toAugmented.left.δ
        (0 : Fin (n + 2)) = barFace (T := T)
        (R := RightModule.regular T) (L := L) n (0 : Fin (n + 2)) := rfl
    rw [hδ]
    exact s_comp_barFace_zero L n
  s_comp_δ := by
    intro n i
    have h_up : (regularBalancedPairing L).toAugmented.left.δ i.succ =
        barFace (T := T) (R := RightModule.regular T) (L := L)
          (n + 1) i.succ := rfl
    have h_low : (regularBalancedPairing L).toAugmented.left.δ i =
        barFace (T := T) (R := RightModule.regular T) (L := L)
          n i := rfl
    rw [h_up, h_low]
    exact s_comp_barFace_succ L n i
  s_comp_σ := s_comp_σ_succ L
@[simp]
theorem extraDegeneracy_s' :
    (extraDegeneracy L).s' = s' L :=
  rfl

@[simp]
theorem extraDegeneracy_s (n : ℕ) :
    (extraDegeneracy L).s n = s L n :=
  rfl

/-- The left extra degeneracy through `ExtraDegeneracy.toSimplicial`. -/
noncomputable def extraDegeneracySimplicial :
    SimplicialObject.Augmented.ExtraDegeneracy
      (BalancedPairing.toSimplicialAugmented
        (regularBalancedPairing L)) where
  s' := (extraDegeneracy L).toSimplicial.s'
  s n := (extraDegeneracy L).toSimplicial.s n
  s'_comp_ε := by
    have hgen := (extraDegeneracy L).toSimplicial.s'_comp_ε
    rw [BalancedPairing.toSimplicialAugmented_hom_app_mk] at ⊢
    rw [SimplicialObject.Data.Augmented.toSimplicialAugmented_hom_app_mk]
      at hgen
    exact hgen
  s₀_comp_δ₁ := by
    have hgen := (extraDegeneracy L).toSimplicial.s₀_comp_δ₁
    have hδ : (BalancedPairing.toSimplicialAugmented
        (regularBalancedPairing L)).left.δ (1 : Fin 2) =
        (SimplicialObject.Data.Augmented.toSimplicialAugmented
          (regularBalancedPairing L).toAugmented).left.δ (1 : Fin 2) :=
      rfl
    rw [hδ, BalancedPairing.toSimplicialAugmented_hom_app_mk] at ⊢
    rw [SimplicialObject.Data.Augmented.toSimplicialAugmented_hom_app_mk]
      at hgen
    exact hgen
  s_comp_δ₀ := by
    intro n
    have hgen := (extraDegeneracy L).toSimplicial.s_comp_δ₀ n
    have hδ : (BalancedPairing.toSimplicialAugmented
        (regularBalancedPairing L)).left.δ (0 : Fin (n + 2)) =
        (SimplicialObject.Data.Augmented.toSimplicialAugmented
          (regularBalancedPairing L).toAugmented).left.δ (0 : Fin (n + 2)) :=
      rfl
    rw [hδ] at ⊢
    exact hgen
  s_comp_δ := by
    intro n i
    have hgen := (extraDegeneracy L).toSimplicial.s_comp_δ n i
    have h_up : (BalancedPairing.toSimplicialAugmented
        (regularBalancedPairing L)).left.δ i.succ =
        (SimplicialObject.Data.Augmented.toSimplicialAugmented
          (regularBalancedPairing L).toAugmented).left.δ i.succ := rfl
    have h_low : (BalancedPairing.toSimplicialAugmented
        (regularBalancedPairing L)).left.δ i =
        (SimplicialObject.Data.Augmented.toSimplicialAugmented
          (regularBalancedPairing L).toAugmented).left.δ i := rfl
    rw [h_up, h_low] at ⊢
    exact hgen
  s_comp_σ := by
    intro n i
    have hgen := (extraDegeneracy L).toSimplicial.s_comp_σ n i
    have h_up : (BalancedPairing.toSimplicialAugmented
        (regularBalancedPairing L)).left.σ i.succ =
        (SimplicialObject.Data.Augmented.toSimplicialAugmented
          (regularBalancedPairing L).toAugmented).left.σ i.succ := rfl
    have h_low : (BalancedPairing.toSimplicialAugmented
        (regularBalancedPairing L)).left.σ i =
        (SimplicialObject.Data.Augmented.toSimplicialAugmented
          (regularBalancedPairing L).toAugmented).left.σ i := rfl
    rw [h_up, h_low] at ⊢
    exact hgen
@[simp]
theorem extraDegeneracySimplicial_s' :
    (extraDegeneracySimplicial L).s' = s' L :=
  rfl
@[simp]
theorem extraDegeneracySimplicial_s (n : ℕ) :
    (extraDegeneracySimplicial L).s n = s L n :=
  rfl
end BarRegularContraction

end Monad
end CategoryTheory
