/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.Monad.BarFunctorial

/-!
# Same-carrier monad-change for iterated powers and the two-sided bar

For `h : T ⟶ S` in `Monad C` define `monadPowHom h n : monadPow T n ⟶ monadPow S n`
recursively, with zero/successor component formulas and identity/composition laws.

Compatibility: `ηᵀ(n,i) ≫ hⁿ⁺¹ = hⁿ ≫ ηˢ(n,i)` and `μᵀ(n,i) ≫ hⁿ = hⁿ⁺¹ ≫ μˢ(n,i)`
via `monadPowHom_etaAtPos_app` / `monadPowHom_muAtPos_app`, plus reversed
wrappers `monadPowHom_barEtaAtPos_app` and `monadPowHom_barMuAtPos_app`.

Then, for `h : T ⟶ S` and `S`-modules `R` and `L`, define the degreewise
`barChangeMap h R L n` from
`barObj T (rightModuleRestrictAlongHom h R) (leftModuleRestrictAlongHom h L) n`
to `barObj S R L n`, with component `R.map ((monadPowHom h n).app (L.obj a))`.
Prove component formula, compatibility with every `barDegeneracy`, middle,
right-endpoint, and left-endpoint `barFace`s, and the unified face theorem
`barChangeMap_barFace`. Package the data-level `barChangeDataHom` and genuine
`barChangeHom`, with identity/composition via the restriction isos
`barDataRestrictIdIso` / `barDataRestrictCompIso` and
`twoSidedBarRestrictIdIso` / `twoSidedBarRestrictCompIso`.
Fixed-`h` naturality is packaged as `barChangeNatTrans`, with simp coherence
`barChangeNatTrans_id_app` / `barChangeNatTrans_comp_app` reusing the
`barChangeHom` laws.
Same-carrier only: no carrier change, outer whiskering, or objectwise
evaluation comparison.
-/

@[expose] public section

namespace CategoryTheory
namespace Monad

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C]

/-- Iterated power comparison along a monad morphism. -/
noncomputable def monadPowHom {T S : Monad C} (h : T ⟶ S) :
    (n : ℕ) → monadPow T n ⟶ monadPow S n
  | 0 => 𝟙 _
  | n + 1 => h.toNatTrans ◫ monadPowHom h n

@[simp]
lemma monadPowHom_zero {T S : Monad C} (h : T ⟶ S) :
    monadPowHom h 0 = 𝟙 _ := rfl

@[simp]
lemma monadPowHom_succ {T S : Monad C} (h : T ⟶ S) (n : ℕ) :
    monadPowHom h (n + 1) = h.toNatTrans ◫ monadPowHom h n := rfl

@[simp]
lemma monadPowHom_zero_app {T S : Monad C} (h : T ⟶ S) (X : C) :
    (monadPowHom h 0).app X = 𝟙 X := rfl

/-- Successor component formula (definitional `hcomp` form). -/
@[simp]
lemma monadPowHom_succ_app {T S : Monad C} (h : T ⟶ S) (n : ℕ) (X : C) :
    (monadPowHom h (n + 1)).app X =
      (monadPowHom h n).app (T.obj X) ≫ (monadPow S n).map (h.app X) := by
  have hdef : (monadPowHom h (n + 1)).app X =
      (h.toNatTrans ◫ monadPowHom h n).app X := rfl
  rw [hdef, NatTrans.hcomp_app]

/-- Alternative successor formula via naturality of the recursive comparison. -/
lemma monadPowHom_succ_app' {T S : Monad C} (h : T ⟶ S) (n : ℕ) (X : C) :
    (monadPowHom h (n + 1)).app X =
      (monadPow T n).map (h.app X) ≫ (monadPowHom h n).app (S.obj X) := by
  have nat := (monadPowHom h n).naturality (h.app X)
  calc
    (monadPowHom h (n + 1)).app X
        = (monadPowHom h n).app (T.obj X) ≫ (monadPow S n).map (h.app X) :=
          monadPowHom_succ_app h n X
    _ = (monadPow T n).map (h.app X) ≫ (monadPowHom h n).app (S.obj X) := by
      rw [nat]

@[simp]
lemma monadPowHom_app_naturality {T S : Monad C} (h : T ⟶ S) (n : ℕ)
    {X Y : C} (f : X ⟶ Y) :
    (monadPow T n).map f ≫ (monadPowHom h n).app Y =
      (monadPowHom h n).app X ≫ (monadPow S n).map f :=
  (monadPowHom h n).naturality f

@[simp]
lemma monadPowHom_naturality_assoc {T S : Monad C} (h : T ⟶ S) (n : ℕ)
    {X Y Z : C} (f : X ⟶ Y) (g : (monadPow S n).obj Y ⟶ Z) :
    (monadPow T n).map f ≫ (monadPowHom h n).app Y ≫ g =
      (monadPowHom h n).app X ≫ (monadPow S n).map f ≫ g := by
  rw [← Category.assoc, monadPowHom_app_naturality, Category.assoc]

/-- Identity law: comparison along `𝟙 T` is identity. -/
@[simp]
theorem monadPowHom_id (T : Monad C) (n : ℕ) :
    monadPowHom (𝟙 T : T ⟶ T) n = 𝟙 (monadPow T n) := by
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    ext X
    have h_succ : (monadPowHom (𝟙 T : T ⟶ T) (n + 1)).app X =
        (monadPowHom (𝟙 T : T ⟶ T) n).app (T.obj X) ≫
          (monadPow T n).map ((𝟙 T : T ⟶ T).app X) :=
      monadPowHom_succ_app (𝟙 T) n X
    rw [h_succ, ih]
    simp

/-- Composition law: comparison along `h ≫ k` composes. -/
@[simp]
theorem monadPowHom_comp {T S U : Monad C} (h : T ⟶ S) (k : S ⟶ U) (n : ℕ) :
    monadPowHom (h ≫ k) n = monadPowHom h n ≫ monadPowHom k n := by
  induction n with
  | zero =>
    ext X
    simp
  | succ n ih =>
    calc
      monadPowHom (h ≫ k) (n + 1)
          = (h ≫ k).toNatTrans ◫ monadPowHom (h ≫ k) n := rfl
      _ = (h.toNatTrans ≫ k.toNatTrans) ◫ (monadPowHom h n ≫ monadPowHom k n) := by
        rw [MonadHom.comp_toNatTrans, ih]
      _ = (h.toNatTrans ◫ monadPowHom h n) ≫ (k.toNatTrans ◫ monadPowHom k n) := by
        rw [NatTrans.exchange]
      _ = monadPowHom h (n + 1) ≫ monadPowHom k (n + 1) := rfl

@[simp]
lemma monadPowHom_comp_app {T S U : Monad C} (h : T ⟶ S) (k : S ⟶ U) (n : ℕ) (X : C) :
    (monadPowHom (h ≫ k) n).app X =
      (monadPowHom h n).app X ≫ (monadPowHom k n).app X := by
  rw [monadPowHom_comp]
  rfl

section EtaCompat

variable {T S : Monad C}

theorem monadPowHom_etaAtPos_app (h : T ⟶ S) (n : ℕ) (i : Fin (n + 1)) (X : C) :
    etaAtPos T n i X ≫ (monadPowHom h (n + 1)).app X =
      (monadPowHom h n).app X ≫ etaAtPos S n i X := by
  induction n generalizing X with
  | zero =>
    have hi : i = ⟨0, by omega⟩ := by ext; omega
    subst hi
    calc
      etaAtPos T 0 ⟨0, by omega⟩ X ≫ (monadPowHom h 1).app X
          = T.η.app X ≫ (monadPowHom h 1).app X := rfl
      _ = T.η.app X ≫ ((monadPowHom h 0).app (T.obj X) ≫ (monadPow S 0).map (h.app X)) := by
        rw [monadPowHom_succ_app]
      _ = (T.η.app X ≫ (monadPowHom h 0).app (T.obj X)) ≫ (monadPow S 0).map (h.app X) := by
            rw [Category.assoc]
      _ = (T.η.app X ≫ 𝟙 (T.obj X)) ≫ (monadPow S 0).map (h.app X) := rfl
      _ = T.η.app X ≫ h.app X := by simp
      _ = S.η.app X := h.app_η X
      _ = 𝟙 X ≫ S.η.app X := by simp
      _ = (monadPowHom h 0).app X ≫ etaAtPos S 0 ⟨0, by omega⟩ X := rfl
  | succ n ih =>
    match i with
    | ⟨0, hi0⟩ =>
      have hetaT : etaAtPos T (n + 1) ⟨0, hi0⟩ X =
          (monadPow T (n + 1)).map (T.η.app X) := rfl
      have hetaS : etaAtPos S (n + 1) ⟨0, hi0⟩ X =
          (monadPow S (n + 1)).map (S.η.app X) := rfl
      have hpow : (monadPowHom h (n + 2)).app X =
          (monadPowHom h (n + 1)).app (T.obj X) ≫
            (monadPow S (n + 1)).map (h.app X) :=
        monadPowHom_succ_app h (n + 1) X
      have natPow : (monadPow T (n + 1)).map (T.η.app X) ≫
          (monadPowHom h (n + 1)).app (T.obj X) =
          (monadPowHom h (n + 1)).app X ≫
            (monadPow S (n + 1)).map (T.η.app X) :=
        monadPowHom_app_naturality h (n + 1) (T.η.app X)
      calc
        etaAtPos T (n + 1) ⟨0, hi0⟩ X ≫ (monadPowHom h (n + 2)).app X
            = (monadPow T (n + 1)).map (T.η.app X) ≫
                (monadPowHom h (n + 2)).app X := by rw [hetaT]
        _ = (monadPow T (n + 1)).map (T.η.app X) ≫
                ((monadPowHom h (n + 1)).app (T.obj X) ≫
                  (monadPow S (n + 1)).map (h.app X)) := by rw [hpow]
        _ = ((monadPow T (n + 1)).map (T.η.app X) ≫
                (monadPowHom h (n + 1)).app (T.obj X)) ≫
                  (monadPow S (n + 1)).map (h.app X) := by
              rw [← Category.assoc]
        _ = ((monadPowHom h (n + 1)).app X ≫
                (monadPow S (n + 1)).map (T.η.app X)) ≫
                  (monadPow S (n + 1)).map (h.app X) := by rw [natPow]
        _ = (monadPowHom h (n + 1)).app X ≫
                ((monadPow S (n + 1)).map (T.η.app X) ≫
                  (monadPow S (n + 1)).map (h.app X)) := by
              rw [Category.assoc]
        _ = (monadPowHom h (n + 1)).app X ≫
                (monadPow S (n + 1)).map (T.η.app X ≫ h.app X) := by
              rw [← (monadPow S (n + 1)).map_comp]
        _ = (monadPowHom h (n + 1)).app X ≫
                (monadPow S (n + 1)).map (S.η.app X) := by rw [h.app_η X]
        _ = (monadPowHom h (n + 1)).app X ≫
                etaAtPos S (n + 1) ⟨0, hi0⟩ X := by rw [hetaS]
    | ⟨k + 1, hk⟩ =>
      let i0 : Fin (n + 1) := ⟨k, by omega⟩
      have hetaT_succ : etaAtPos T (n + 1) ⟨k + 1, hk⟩ X =
          etaAtPos T n i0 (T.obj X) := rfl
      have hetaS_succ : etaAtPos S (n + 1) ⟨k + 1, hk⟩ X =
          etaAtPos S n i0 (S.obj X) := rfl
      have hpow2 : (monadPowHom h (n + 2)).app X =
          (monadPow T (n + 1)).map (h.app X) ≫
            (monadPowHom h (n + 1)).app (S.obj X) :=
        monadPowHom_succ_app' h (n + 1) X
      have hpow1 : (monadPowHom h (n + 1)).app X =
          (monadPow T n).map (h.app X) ≫
            (monadPowHom h n).app (S.obj X) :=
        monadPowHom_succ_app' h n X
      have etaNat : etaAtPos T n i0 (T.obj X) ≫
          (monadPow T (n + 1)).map (h.app X) =
          (monadPow T n).map (h.app X) ≫
            etaAtPos T n i0 (S.obj X) := by
        have := etaAtPos_naturality T n i0 (f := h.app X)
        exact this.symm
      calc
        etaAtPos T (n + 1) ⟨k + 1, hk⟩ X ≫ (monadPowHom h (n + 2)).app X
            = etaAtPos T n i0 (T.obj X) ≫ (monadPowHom h (n + 2)).app X := by
              rw [hetaT_succ]
        _ = etaAtPos T n i0 (T.obj X) ≫
                ((monadPow T (n + 1)).map (h.app X) ≫
                  (monadPowHom h (n + 1)).app (S.obj X)) := by
              rw [hpow2]
        _ = (etaAtPos T n i0 (T.obj X) ≫
                (monadPow T (n + 1)).map (h.app X)) ≫
                  (monadPowHom h (n + 1)).app (S.obj X) := by
              rw [Category.assoc]
        _ = ((monadPow T n).map (h.app X) ≫
                etaAtPos T n i0 (S.obj X)) ≫
                  (monadPowHom h (n + 1)).app (S.obj X) := by
              rw [etaNat]
        _ = (monadPow T n).map (h.app X) ≫
                (etaAtPos T n i0 (S.obj X) ≫
                  (monadPowHom h (n + 1)).app (S.obj X)) := by
              rw [← Category.assoc]
        _ = (monadPow T n).map (h.app X) ≫
                ((monadPowHom h n).app (S.obj X) ≫
                  etaAtPos S n i0 (S.obj X)) := by
              rw [ih i0 (S.obj X)]
        _ = ((monadPow T n).map (h.app X) ≫
                (monadPowHom h n).app (S.obj X)) ≫
                  etaAtPos S n i0 (S.obj X) := by
              rw [Category.assoc]
        _ = (monadPowHom h (n + 1)).app X ≫
                etaAtPos S n i0 (S.obj X) := by
              rw [hpow1]
        _ = (monadPowHom h (n + 1)).app X ≫
                etaAtPos S (n + 1) ⟨k + 1, hk⟩ X := by
              rw [hetaS_succ]

theorem monadPowHom_barEtaAtPos_app (h : T ⟶ S) (n : ℕ) (i : Fin (n + 1)) (X : C) :
    barEtaAtPos T n i X ≫ (monadPowHom h (n + 1)).app X =
      (monadPowHom h n).app X ≫ barEtaAtPos S n i X := by
  simp only [barEtaAtPos]
  exact monadPowHom_etaAtPos_app h n i.rev X

end EtaCompat

section MuCompat

variable {T S : Monad C}

theorem monadPowHom_muAtPos_app (h : T ⟶ S) (n : ℕ) (i : Fin n) (X : C) :
    muAtPos T n i X ≫ (monadPowHom h n).app X =
      (monadPowHom h (n + 1)).app X ≫ muAtPos S n i X := by
  induction n generalizing X with
  | zero =>
    exact isEmptyElim i
  | succ n ih =>
    match i with
    | ⟨0, hi0⟩ =>
      have hmuT : muAtPos T (n + 1) ⟨0, hi0⟩ X =
          (monadPow T n).map (T.μ.app X) := rfl
      have hmuS : muAtPos S (n + 1) ⟨0, hi0⟩ X =
          (monadPow S n).map (S.μ.app X) := rfl
      have hpow1 : (monadPowHom h (n + 1)).app X =
          (monadPowHom h n).app (T.obj X) ≫
            (monadPow S n).map (h.app X) :=
        monadPowHom_succ_app h n X
      have hpow2' : (monadPowHom h (n + 2)).app X =
          (monadPow T (n + 1)).map (h.app X) ≫
            (monadPowHom h (n + 1)).app (S.obj X) :=
        monadPowHom_succ_app' h (n + 1) X
      have natPowMu : (monadPow T n).map (T.μ.app X) ≫
          (monadPowHom h n).app (T.obj X) =
          (monadPowHom h n).app (T.obj (T.obj X)) ≫
            (monadPow S n).map (T.μ.app X) :=
        monadPowHom_app_naturality h n (T.μ.app X)
      have natPowTmap : (monadPow T n).map (T.map (h.app X)) ≫
          (monadPowHom h n).app (T.obj (S.obj X)) =
          (monadPowHom h n).app (T.obj (T.obj X)) ≫
            (monadPow S n).map (T.map (h.app X)) :=
        monadPowHom_app_naturality h n (T.map (h.app X))
      have hComp : (monadPow T (n + 1)).map (h.app X) =
          (monadPow T n).map (T.map (h.app X)) := rfl
      calc
        muAtPos T (n + 1) ⟨0, hi0⟩ X ≫ (monadPowHom h (n + 1)).app X
            = (monadPow T n).map (T.μ.app X) ≫ (monadPowHom h (n + 1)).app X := by
              rw [hmuT]
        _ = (monadPow T n).map (T.μ.app X) ≫
                ((monadPowHom h n).app (T.obj X) ≫
                  (monadPow S n).map (h.app X)) := by
              rw [hpow1]
        _ = ((monadPow T n).map (T.μ.app X) ≫
                (monadPowHom h n).app (T.obj X)) ≫
                  (monadPow S n).map (h.app X) := by
              rw [Category.assoc]
        _ = ((monadPowHom h n).app (T.obj (T.obj X)) ≫
                (monadPow S n).map (T.μ.app X)) ≫
                  (monadPow S n).map (h.app X) := by
              rw [natPowMu]
        _ = (monadPowHom h n).app (T.obj (T.obj X)) ≫
                ((monadPow S n).map (T.μ.app X) ≫
                  (monadPow S n).map (h.app X)) := by
              rw [← Category.assoc]
        _ = (monadPowHom h n).app (T.obj (T.obj X)) ≫
                (monadPow S n).map (T.μ.app X ≫ h.app X) := by
              rw [← (monadPow S n).map_comp]
        _ = (monadPowHom h n).app (T.obj (T.obj X)) ≫
                (monadPow S n).map ((T.map (h.app X) ≫ h.app (S.obj X)) ≫ S.μ.app X) := by
              rw [h.app_μ X]
        _ = (monadPowHom h n).app (T.obj (T.obj X)) ≫
                ((monadPow S n).map (T.map (h.app X) ≫ h.app (S.obj X)) ≫
                  (monadPow S n).map (S.μ.app X)) := by
              rw [(monadPow S n).map_comp]
        _ = (monadPowHom h n).app (T.obj (T.obj X)) ≫
                (((monadPow S n).map (T.map (h.app X)) ≫
                  (monadPow S n).map (h.app (S.obj X))) ≫
                    (monadPow S n).map (S.μ.app X)) := by
              rw [(monadPow S n).map_comp, Category.assoc]
        _ = ((monadPowHom h n).app (T.obj (T.obj X)) ≫
                (monadPow S n).map (T.map (h.app X))) ≫
                (monadPow S n).map (h.app (S.obj X)) ≫
                  (monadPow S n).map (S.μ.app X) := by
              rw [Category.assoc, Category.assoc]
        _ = ((monadPow T n).map (T.map (h.app X)) ≫
                (monadPowHom h n).app (T.obj (S.obj X))) ≫
                (monadPow S n).map (h.app (S.obj X)) ≫
                  (monadPow S n).map (S.μ.app X) := by
              rw [← natPowTmap]
        _ = (monadPow T n).map (T.map (h.app X)) ≫
                ((monadPowHom h n).app (T.obj (S.obj X)) ≫
                  (monadPow S n).map (h.app (S.obj X))) ≫
                  (monadPow S n).map (S.μ.app X) := by
              simp only [Category.assoc]
        _ = (monadPow T n).map (T.map (h.app X)) ≫
                (monadPowHom h (n + 1)).app (S.obj X) ≫
                  (monadPow S n).map (S.μ.app X) := by
              rw [← monadPowHom_succ_app]
        _ = (monadPow T (n + 1)).map (h.app X) ≫
                (monadPowHom h (n + 1)).app (S.obj X) ≫
                  (monadPow S n).map (S.μ.app X) := by
              rw [← hComp]
        _ = ((monadPow T (n + 1)).map (h.app X) ≫
                (monadPowHom h (n + 1)).app (S.obj X)) ≫
                  (monadPow S n).map (S.μ.app X) := by
              rw [Category.assoc]
        _ = (monadPowHom h (n + 2)).app X ≫ (monadPow S n).map (S.μ.app X) := by
              rw [← hpow2']
        _ = (monadPowHom h (n + 2)).app X ≫ muAtPos S (n + 1) ⟨0, hi0⟩ X := by
              rw [hmuS]
    | ⟨k + 1, hk⟩ =>
      let i0 : Fin n := ⟨k, by omega⟩
      have hmuT_succ : muAtPos T (n + 1) ⟨k + 1, hk⟩ X =
          muAtPos T n i0 (T.obj X) := rfl
      have hmuS_succ : muAtPos S (n + 1) ⟨k + 1, hk⟩ X =
          muAtPos S n i0 (S.obj X) := rfl
      have hpow1 : (monadPowHom h (n + 1)).app X =
          (monadPowHom h n).app (T.obj X) ≫
            (monadPow S n).map (h.app X) :=
        monadPowHom_succ_app h n X
      have hpow2 : (monadPowHom h (n + 2)).app X =
          (monadPowHom h (n + 1)).app (T.obj X) ≫
            (monadPow S (n + 1)).map (h.app X) :=
        monadPowHom_succ_app h (n + 1) X
      have muNatS : (monadPow S (n + 1)).map (h.app X) ≫ muAtPos S n i0 (S.obj X) =
          muAtPos S n i0 (T.obj X) ≫ (monadPow S n).map (h.app X) :=
        muAtPos_naturality S n i0 (f := h.app X)
      calc
        muAtPos T (n + 1) ⟨k + 1, hk⟩ X ≫ (monadPowHom h (n + 1)).app X
            = muAtPos T n i0 (T.obj X) ≫ (monadPowHom h (n + 1)).app X := by
              rw [hmuT_succ]
        _ = muAtPos T n i0 (T.obj X) ≫
                ((monadPowHom h n).app (T.obj X) ≫
                  (monadPow S n).map (h.app X)) := by
              rw [hpow1]
        _ = (muAtPos T n i0 (T.obj X) ≫
                (monadPowHom h n).app (T.obj X)) ≫
                  (monadPow S n).map (h.app X) := by
              rw [Category.assoc]
        _ = ((monadPowHom h (n + 1)).app (T.obj X) ≫
                muAtPos S n i0 (T.obj X)) ≫
                  (monadPow S n).map (h.app X) := by
              rw [ih i0 (T.obj X)]
        _ = (monadPowHom h (n + 1)).app (T.obj X) ≫
                (muAtPos S n i0 (T.obj X) ≫
                  (monadPow S n).map (h.app X)) := by
              rw [← Category.assoc]
        _ = (monadPowHom h (n + 1)).app (T.obj X) ≫
                ((monadPow S (n + 1)).map (h.app X) ≫
                  muAtPos S n i0 (S.obj X)) := by
              rw [muNatS]
        _ = ((monadPowHom h (n + 1)).app (T.obj X) ≫
                (monadPow S (n + 1)).map (h.app X)) ≫
                  muAtPos S n i0 (S.obj X) := by
              rw [Category.assoc]
        _ = (monadPowHom h (n + 2)).app X ≫ muAtPos S n i0 (S.obj X) := by
              rw [hpow2]
        _ = (monadPowHom h (n + 2)).app X ≫ muAtPos S (n + 1) ⟨k + 1, hk⟩ X := by
              rw [hmuS_succ]

theorem monadPowHom_barMuAtPos_app (h : T ⟶ S) (n : ℕ) (i : Fin n) (X : C) :
    barMuAtPos T n i X ≫ (monadPowHom h n).app X =
      (monadPowHom h (n + 1)).app X ≫ barMuAtPos S n i X := by
  simp only [barMuAtPos]
  exact monadPowHom_muAtPos_app h n i.rev X

end MuCompat

section BarChangeMap

universe v₂ v₃ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {A : Type u₃} [Category.{v₃} A]
variable {T S : Monad C}

noncomputable def barChangeMap {T S : Monad C} (h : T ⟶ S) (R : RightModule S D)
    (L : LeftModule A S) (n : ℕ) :
    barObj T ((rightModuleRestrictAlongHom (D := D) h).obj R)
      ((leftModuleRestrictAlongHom (A := A) h).obj L) n ⟶
      barObj S R L n where
  app a := R.functor.map ((monadPowHom h n).app (L.functor.obj a))
  naturality a b f := by
    have h_pow_nat :
        (monadPow T n).map (L.functor.map f) ≫
          (monadPowHom h n).app (L.functor.obj b) =
        (monadPowHom h n).app (L.functor.obj a) ≫ (monadPow S n).map (L.functor.map f) :=
      (monadPowHom h n).naturality (L.functor.map f)
    calc
      R.functor.map ((monadPow T n).map (L.functor.map f)) ≫
          R.functor.map ((monadPowHom h n).app (L.functor.obj b))
          = R.functor.map ((monadPow T n).map (L.functor.map f) ≫
              (monadPowHom h n).app (L.functor.obj b)) := by
            rw [← R.functor.map_comp]
      _ = R.functor.map ((monadPowHom h n).app (L.functor.obj a) ≫
              (monadPow S n).map (L.functor.map f)) := by
            rw [h_pow_nat]
      _ = R.functor.map ((monadPowHom h n).app (L.functor.obj a)) ≫
              R.functor.map ((monadPow S n).map (L.functor.map f)) := by
            rw [R.functor.map_comp]

@[simp]
lemma barChangeMap_app {T S : Monad C} {D : Type u₂} [Category.{v₂} D] {A : Type u₃}
    [Category.{v₃} A] (h : T ⟶ S) (R : RightModule S D) (L : LeftModule A S) (n : ℕ)
    (a : A) :
    (barChangeMap (D := D) (A := A) h R L n).app a =
      R.functor.map ((monadPowHom h n).app (L.functor.obj a)) := rfl

/-! Degeneracy compatibility – uses `monadPowHom_barEtaAtPos_app` and `rfl` restriction lemmas -/

theorem barChangeMap_barDegeneracy (h : T ⟶ S) (R : RightModule S D)
    (L : LeftModule A S) (n : ℕ) (i : Fin (n + 1)) :
    barChangeMap (D := D) (A := A) h R L n ≫ barDegeneracy (T := S) (R := R) (L := L) n i =
    barDegeneracy (T := T)
        (R := (rightModuleRestrictAlongHom (D := D) h).obj R)
        (L := (leftModuleRestrictAlongHom (A := A) h).obj L) n i ≫
      barChangeMap (D := D) (A := A) h R L (n + 1) := by
  ext a
  simp only [barChangeMap_app, barDegeneracy_app, NatTrans.comp_app]
  have h_pow : barEtaAtPos T n i (L.functor.obj a) ≫ (monadPowHom h (n + 1)).app (L.functor.obj a) =
      (monadPowHom h n).app (L.functor.obj a) ≫ barEtaAtPos S n i (L.functor.obj a) :=
    monadPowHom_barEtaAtPos_app h n i (L.functor.obj a)
  calc
    R.functor.map ((monadPowHom h n).app (L.functor.obj a)) ≫
        R.functor.map (barEtaAtPos S n i (L.functor.obj a))
        = R.functor.map ((monadPowHom h n).app (L.functor.obj a) ≫
            barEtaAtPos S n i (L.functor.obj a)) := by
          rw [← R.functor.map_comp]
    _ = R.functor.map (barEtaAtPos T n i (L.functor.obj a) ≫
            (monadPowHom h (n + 1)).app (L.functor.obj a)) := by
          rw [← h_pow]
    _ = R.functor.map (barEtaAtPos T n i (L.functor.obj a)) ≫
            R.functor.map ((monadPowHom h (n + 1)).app (L.functor.obj a)) := by
          rw [R.functor.map_comp]

/-! Middle faces (inner multiplications) – uses `monadPowHom_barMuAtPos_app`
and `rfl` restriction lemmas -/

theorem barChangeMap_barFace_middle (h : T ⟶ S) (R : RightModule S D)
    (L : LeftModule A S) (n : ℕ) (k : Fin n) :
    let i : Fin (n + 2) := ⟨k.val + 1, by omega⟩
    barChangeMap (D := D) (A := A) h R L (n + 1) ≫ barFace (T := S) (R := R) (L := L) n i =
    barFace (T := T)
        (R := (rightModuleRestrictAlongHom (D := D) h).obj R)
        (L := (leftModuleRestrictAlongHom (A := A) h).obj L) n i ≫
      barChangeMap (D := D) (A := A) h R L n := by
  intro i
  ext a
  simp only [barChangeMap_app, NatTrans.comp_app]
  -- The middle face depends only on the underlying `val`; reconcile the
  -- `by omega` proof with the `lt_trans` proof used in `barFace_middle`.
  have hi_eq : i =
      (⟨k.val + 1,
        Nat.lt_trans (Nat.succ_lt_succ k.isLt) (Nat.lt_succ_self _)⟩ : Fin (n + 2)) := by
    apply Fin.ext
    simp [i]
  have h_face_S : (barFace (T := S) (R := R) (L := L) n i).app a =
      R.functor.map (barMuAtPos S n k (L.functor.obj a)) := by
    rw [hi_eq]
    exact barFace_middle (T := S) (R := R) (L := L) n k a
  have h_face_T : (barFace (T := T)
      (R := (rightModuleRestrictAlongHom (D := D) h).obj R)
      (L := (leftModuleRestrictAlongHom (A := A) h).obj L) n i).app a =
      R.functor.map (barMuAtPos T n k (L.functor.obj a)) := by
    have h_mid :
        (barFace (T := T)
          (R := (rightModuleRestrictAlongHom (D := D) h).obj R)
          (L := (leftModuleRestrictAlongHom (A := A) h).obj L) n i).app a =
        ((rightModuleRestrictAlongHom (D := D) h).obj R).functor.map
          (barMuAtPos T n k
            (((leftModuleRestrictAlongHom (A := A) h).obj L).functor.obj a)) := by
      rw [hi_eq]
      exact barFace_middle (T := T)
        (R := (rightModuleRestrictAlongHom (D := D) h).obj R)
        (L := (leftModuleRestrictAlongHom (A := A) h).obj L) n k a
    have h_eq2 :
        ((rightModuleRestrictAlongHom (D := D) h).obj R).functor.map
            (barMuAtPos T n k
              (((leftModuleRestrictAlongHom (A := A) h).obj L).functor.obj a)) =
          R.functor.map (barMuAtPos T n k (L.functor.obj a)) := by
      simp only [leftModuleRestrictAlongHom_obj_functor,
        rightModuleRestrictAlongHom_obj_functor]
    exact h_mid.trans h_eq2
  simp only [h_face_T, h_face_S]
  have h_mu : barMuAtPos T n k (L.functor.obj a) ≫ (monadPowHom h n).app (L.functor.obj a) =
      (monadPowHom h (n + 1)).app (L.functor.obj a) ≫ barMuAtPos S n k (L.functor.obj a) :=
    monadPowHom_barMuAtPos_app h n k (L.functor.obj a)
  calc
    R.functor.map ((monadPowHom h (n + 1)).app (L.functor.obj a)) ≫
        R.functor.map (barMuAtPos S n k (L.functor.obj a))
        = R.functor.map ((monadPowHom h (n + 1)).app (L.functor.obj a) ≫
            barMuAtPos S n k (L.functor.obj a)) := by
          rw [← R.functor.map_comp]
    _ = R.functor.map (barMuAtPos T n k (L.functor.obj a) ≫
            (monadPowHom h n).app (L.functor.obj a)) := by
          rw [← h_mu]
    _ = R.functor.map (barMuAtPos T n k (L.functor.obj a)) ≫
            R.functor.map ((monadPowHom h n).app (L.functor.obj a)) := by
          rw [R.functor.map_comp]

/-! Right endpoint `d₀` – reusable `rightActionPow` after restriction -/

theorem rightActionPow_restrictAlongHom {T S : Monad C} {D : Type u₂} [Category.{v₂} D]
    (h : T ⟶ S) (R : RightModule S D) (n : ℕ) (X : C) :
    R.functor.map ((monadPowHom h (n + 1)).app X) ≫ rightActionPow S R n X =
    rightActionPow T ((rightModuleRestrictAlongHom (D := D) h).obj R) n X ≫
      R.functor.map ((monadPowHom h n).app X) := by
  induction n generalizing X with
  | zero =>
    simp only [monadPowHom_succ_app, monadPowHom_zero_app, rightActionPow_zero,
      rightModuleRestrictAlongHom_obj_action_app]
    simp
  | succ n ih =>
    let R' := (rightModuleRestrictAlongHom (D := D) h).obj R
    have h_succ_app : (monadPowHom h (n + 2)).app X =
        (monadPowHom h (n + 1)).app (T.obj X) ≫ (monadPow S (n + 1)).map (h.app X) :=
      monadPowHom_succ_app h (n + 1) X
    have h_succ_pow_S : rightActionPow S R (n + 1) X = rightActionPow S R n (S.obj X) := rfl
    have h_succ_pow_T : rightActionPow T R' (n + 1) X = rightActionPow T R' n (T.obj X) := rfl
    have h_pow_app : (monadPowHom h (n + 1)).app X =
        (monadPowHom h n).app (T.obj X) ≫ (monadPow S n).map (h.app X) :=
      monadPowHom_succ_app h n X
    rw [h_succ_app, h_succ_pow_S, h_succ_pow_T, h_pow_app]
    have h_map : R.functor.map ((monadPowHom h (n + 1)).app (T.obj X) ≫
        (monadPow S (n + 1)).map (h.app X)) =
        R.functor.map ((monadPowHom h (n + 1)).app (T.obj X)) ≫
          R.functor.map ((monadPow S (n + 1)).map (h.app X)) :=
      R.functor.map_comp _ _
    -- Explicit calc using `congrArg` and `Category.assoc` to avoid `rw` leaving rfl goals
    -- that confuse `calc`'s `Trans` synthesis.
    have step1 : R.functor.map ((monadPowHom h (n + 1)).app (T.obj X) ≫
          (monadPow S (n + 1)).map (h.app X)) ≫ rightActionPow S R n (S.obj X) =
        (R.functor.map ((monadPowHom h (n + 1)).app (T.obj X)) ≫
          R.functor.map ((monadPow S (n + 1)).map (h.app X))) ≫
        rightActionPow S R n (S.obj X) :=
      congrArg (· ≫ rightActionPow S R n (S.obj X)) h_map
    have step2 : (R.functor.map ((monadPowHom h (n + 1)).app (T.obj X)) ≫
          R.functor.map ((monadPow S (n + 1)).map (h.app X))) ≫
        rightActionPow S R n (S.obj X) =
        R.functor.map ((monadPowHom h (n + 1)).app (T.obj X)) ≫
          (R.functor.map ((monadPow S (n + 1)).map (h.app X)) ≫
            rightActionPow S R n (S.obj X)) :=
      Category.assoc _ _ _
    have h_nat : R.functor.map ((monadPow S (n + 1)).map (h.app X)) ≫
        rightActionPow S R n (S.obj X) =
        rightActionPow S R n (T.obj X) ≫
          R.functor.map ((monadPow S n).map (h.app X)) :=
      rightActionPow_naturality S R n (h.app X)
    have step3 : R.functor.map ((monadPowHom h (n + 1)).app (T.obj X)) ≫
          (R.functor.map ((monadPow S (n + 1)).map (h.app X)) ≫
            rightActionPow S R n (S.obj X)) =
        R.functor.map ((monadPowHom h (n + 1)).app (T.obj X)) ≫
          (rightActionPow S R n (T.obj X) ≫
            R.functor.map ((monadPow S n).map (h.app X))) :=
      congrArg (R.functor.map ((monadPowHom h (n + 1)).app (T.obj X)) ≫ ·) h_nat
    have step4 : R.functor.map ((monadPowHom h (n + 1)).app (T.obj X)) ≫
          (rightActionPow S R n (T.obj X) ≫
            R.functor.map ((monadPow S n).map (h.app X))) =
        (R.functor.map ((monadPowHom h (n + 1)).app (T.obj X)) ≫
          rightActionPow S R n (T.obj X)) ≫
        R.functor.map ((monadPow S n).map (h.app X)) :=
      (Category.assoc _ _ _).symm
    have step5 : (R.functor.map ((monadPowHom h (n + 1)).app (T.obj X)) ≫
          rightActionPow S R n (T.obj X)) ≫
        R.functor.map ((monadPow S n).map (h.app X)) =
        (rightActionPow T R' n (T.obj X) ≫
          R.functor.map ((monadPowHom h n).app (T.obj X))) ≫
        R.functor.map ((monadPow S n).map (h.app X)) :=
      congrArg (· ≫ R.functor.map ((monadPow S n).map (h.app X))) (ih (T.obj X))
    have step6 : (rightActionPow T R' n (T.obj X) ≫
          R.functor.map ((monadPowHom h n).app (T.obj X))) ≫
        R.functor.map ((monadPow S n).map (h.app X)) =
        rightActionPow T R' n (T.obj X) ≫
          (R.functor.map ((monadPowHom h n).app (T.obj X)) ≫
            R.functor.map ((monadPow S n).map (h.app X))) :=
      Category.assoc _ _ _
    have step7 : R.functor.map ((monadPowHom h n).app (T.obj X)) ≫
          R.functor.map ((monadPow S n).map (h.app X)) =
        R.functor.map ((monadPowHom h n).app (T.obj X) ≫
          (monadPow S n).map (h.app X)) :=
      (R.functor.map_comp _ _).symm
    have step7' : rightActionPow T R' n (T.obj X) ≫
          (R.functor.map ((monadPowHom h n).app (T.obj X)) ≫
            R.functor.map ((monadPow S n).map (h.app X))) =
        rightActionPow T R' n (T.obj X) ≫
          R.functor.map ((monadPowHom h n).app (T.obj X) ≫
            (monadPow S n).map (h.app X)) :=
      congrArg (rightActionPow T R' n (T.obj X) ≫ ·) step7
    exact step1.trans (step2.trans (step3.trans (step4.trans
      (step5.trans (step6.trans step7')))))

/-! Right endpoint compatibility `d₀` -/

theorem barChangeMap_barFace_zero (h : T ⟶ S) (R : RightModule S D)
    (L : LeftModule A S) (n : ℕ) :
    barChangeMap (D := D) (A := A) h R L (n + 1) ≫
      barFace (T := S) (R := R) (L := L) n ⟨0, by omega⟩ =
    barFace (T := T)
      (R := (rightModuleRestrictAlongHom (D := D) h).obj R)
      (L := (leftModuleRestrictAlongHom (A := A) h).obj L) n ⟨0, by omega⟩ ≫
      barChangeMap (D := D) (A := A) h R L n := by
  ext a
  simp only [barChangeMap_app, NatTrans.comp_app, barFace_right]
  exact rightActionPow_restrictAlongHom (D := D) h R n (L.functor.obj a)

/-! Left endpoint compatibility `d_{n+1}` -/

theorem barChangeMap_barFace_last (h : T ⟶ S) (R : RightModule S D)
    (L : LeftModule A S) (n : ℕ) :
    barChangeMap (D := D) (A := A) h R L (n + 1) ≫
      barFace (T := S) (R := R) (L := L) n ⟨n + 1, by omega⟩ =
    barFace (T := T)
      (R := (rightModuleRestrictAlongHom (D := D) h).obj R)
      (L := (leftModuleRestrictAlongHom (A := A) h).obj L) n ⟨n + 1, by omega⟩ ≫
      barChangeMap (D := D) (A := A) h R L n := by
  ext a
  simp only [barChangeMap_app, NatTrans.comp_app, barFace_left,
    leftModuleRestrictAlongHom_obj_action_app, rightModuleRestrictAlongHom_obj_functor,
    leftModuleRestrictAlongHom_obj_functor]
  have h_pow : (monadPowHom h (n + 1)).app (L.functor.obj a) =
      (monadPow T n).map (h.app (L.functor.obj a)) ≫
        (monadPowHom h n).app (S.obj (L.functor.obj a)) :=
    monadPowHom_succ_app' h n (L.functor.obj a)
  have h_nat : (monadPow T n).map (L.action.app a) ≫ (monadPowHom h n).app (L.functor.obj a) =
      (monadPowHom h n).app (S.obj (L.functor.obj a)) ≫ (monadPow S n).map (L.action.app a) :=
    (monadPowHom h n).naturality (L.action.app a)
  calc
    R.functor.map ((monadPowHom h (n + 1)).app (L.functor.obj a)) ≫
        R.functor.map ((monadPow S n).map (L.action.app a))
        = R.functor.map ((monadPowHom h (n + 1)).app (L.functor.obj a) ≫
          (monadPow S n).map (L.action.app a)) := by rw [← R.functor.map_comp]
    _ = R.functor.map (((monadPow T n).map (h.app (L.functor.obj a)) ≫
          (monadPowHom h n).app (S.obj (L.functor.obj a))) ≫
          (monadPow S n).map (L.action.app a)) := by rw [h_pow]
    _ = R.functor.map ((monadPow T n).map (h.app (L.functor.obj a)) ≫
          ((monadPowHom h n).app (S.obj (L.functor.obj a)) ≫
            (monadPow S n).map (L.action.app a))) := by rw [Category.assoc]
    _ = R.functor.map ((monadPow T n).map (h.app (L.functor.obj a)) ≫
          ((monadPow T n).map (L.action.app a) ≫ (monadPowHom h n).app (L.functor.obj a))) := by
          rw [← h_nat]
    _ = R.functor.map (((monadPow T n).map (h.app (L.functor.obj a)) ≫
          (monadPow T n).map (L.action.app a)) ≫ (monadPowHom h n).app (L.functor.obj a)) := by
          rw [Category.assoc]
    _ = R.functor.map ((monadPow T n).map (h.app (L.functor.obj a) ≫ L.action.app a) ≫
          (monadPowHom h n).app (L.functor.obj a)) := by rw [← (monadPow T n).map_comp]
    _ = R.functor.map ((monadPow T n).map (h.app (L.functor.obj a) ≫ L.action.app a)) ≫
          R.functor.map ((monadPowHom h n).app (L.functor.obj a)) := by rw [R.functor.map_comp]

/-! Unified face compatibility for arbitrary `j : Fin (n+2)` -/

theorem barChangeMap_barFace (h : T ⟶ S) (R : RightModule S D)
    (L : LeftModule A S) (n : ℕ) (j : Fin (n + 2)) :
    barChangeMap (D := D) (A := A) h R L (n + 1) ≫
      barFace (T := S) (R := R) (L := L) n j =
    barFace (T := T)
      (R := (rightModuleRestrictAlongHom (D := D) h).obj R)
      (L := (leftModuleRestrictAlongHom (A := A) h).obj L) n j ≫
      barChangeMap (D := D) (A := A) h R L n := by
  by_cases h0 : j.val = 0
  · have hj : j = ⟨0, by omega⟩ := by
      apply Fin.ext
      omega
    rw [hj]
    exact barChangeMap_barFace_zero h R L n
  · by_cases hlast : j.val = n + 1
    · have hj : j = ⟨n + 1, by omega⟩ := by
        apply Fin.ext
        omega
      rw [hj]
      exact barChangeMap_barFace_last h R L n
    · have hk_lt : j.val - 1 < n := by omega
      let k : Fin n := ⟨j.val - 1, hk_lt⟩
      have hj_eq : j = ⟨k.val + 1, by omega⟩ := by
        apply Fin.ext
        simp only [k]
        omega
      rw [hj_eq]
      exact barChangeMap_barFace_middle h R L n k

/-! Packaged data-level morphism -/

noncomputable def barChangeDataHom {T S : Monad C} (h : T ⟶ S)
    (R : RightModule S D) (L : LeftModule A S) :
    barData T ((rightModuleRestrictAlongHom (D := D) h).obj R)
      ((leftModuleRestrictAlongHom (A := A) h).obj L) ⟶
      barData S R L where
  app n := barChangeMap (D := D) (A := A) h R L n
  w_δ := fun i => barChangeMap_barFace (D := D) (A := A) h R L _ i
  w_σ := fun i => barChangeMap_barDegeneracy (D := D) (A := A) h R L _ i

@[simp]
lemma barChangeDataHom_app {T S : Monad C} (h : T ⟶ S)
    (R : RightModule S D) (L : LeftModule A S) (n : ℕ) :
    (barChangeDataHom (D := D) (A := A) h R L).app n =
      barChangeMap (D := D) (A := A) h R L n := rfl

@[simp]
lemma barChangeDataHom_app_app {T S : Monad C} (h : T ⟶ S)
    (R : RightModule S D) (L : LeftModule A S) (n : ℕ) (a : A) :
    ((barChangeDataHom (D := D) (A := A) h R L).app n).app a =
      R.functor.map ((monadPowHom h n).app (L.functor.obj a)) := rfl

end BarChangeMap

section BarChangeHom

universe v₂ v₃ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {A : Type u₃} [Category.{v₃} A]
variable {T S : Monad C}

/-- Genuine simplicial morphism induced by a same-carrier monad change,
via the generic `Data.toSimplicialObject` transport. -/
noncomputable def barChangeHom (h : T ⟶ S) (R : RightModule S D)
    (L : LeftModule A S) :
    twoSidedBar T ((rightModuleRestrictAlongHom (D := D) h).obj R)
      ((leftModuleRestrictAlongHom (A := A) h).obj L) ⟶
      twoSidedBar S R L :=
  SimplicialObject.Data.toSimplicialNatTrans (barChangeDataHom (D := D) (A := A) h R L)

@[simp]
theorem barChangeHom_app_op_mk (h : T ⟶ S) (R : RightModule S D)
    (L : LeftModule A S) (n : ℕ) :
    (barChangeHom (D := D) (A := A) h R L).app (Opposite.op (SimplexCategory.mk n)) =
      barChangeMap (D := D) (A := A) h R L n :=
  rfl

theorem barChangeHom_app (h : T ⟶ S) (R : RightModule S D)
    (L : LeftModule A S) (Δ : SimplexCategoryᵒᵖ) :
    (barChangeHom (D := D) (A := A) h R L).app Δ =
      barChangeMap (D := D) (A := A) h R L (Opposite.unop Δ).len := by
  obtain ⟨Δ⟩ := Δ
  rfl

@[simp]
theorem barChangeHom_app_len (h : T ⟶ S) (R : RightModule S D)
    (L : LeftModule A S) (Δ : SimplexCategoryᵒᵖ) :
    (barChangeHom (D := D) (A := A) h R L).app Δ =
      barChangeMap (D := D) (A := A) h R L (Opposite.unop Δ).len :=
  barChangeHom_app (D := D) (A := A) h R L Δ

@[simp]
theorem barChangeHom_app_app_op_mk (h : T ⟶ S) (R : RightModule S D)
    (L : LeftModule A S) (n : ℕ) (a : A) :
    ((barChangeHom (D := D) (A := A) h R L).app (Opposite.op (SimplexCategory.mk n))).app a =
      R.functor.map ((monadPowHom h n).app (L.functor.obj a)) :=
  rfl

theorem barChangeHom_app_app (h : T ⟶ S) (R : RightModule S D)
    (L : LeftModule A S) (Δ : SimplexCategoryᵒᵖ) (a : A) :
    ((barChangeHom (D := D) (A := A) h R L).app Δ).app a =
      R.functor.map ((monadPowHom h (Opposite.unop Δ).len).app (L.functor.obj a)) := by
  obtain ⟨Δ⟩ := Δ
  rfl

@[simp]
theorem barChangeHom_app_app_len (h : T ⟶ S) (R : RightModule S D)
    (L : LeftModule A S) (Δ : SimplexCategoryᵒᵖ) (a : A) :
    ((barChangeHom (D := D) (A := A) h R L).app Δ).app a =
      R.functor.map ((monadPowHom h (Opposite.unop Δ).len).app (L.functor.obj a)) :=
  barChangeHom_app_app (D := D) (A := A) h R L Δ a

end BarChangeHom

section BarChangeMapLaws

universe v₂ v₃ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {A : Type u₃} [Category.{v₃} A]
variable {T S U : Monad C}

@[simp]
theorem barChangeMap_id_app (R : RightModule T D) (L : LeftModule A T) (n : ℕ) (a : A) :
    (barChangeMap (D := D) (A := A) (𝟙 T) R L n).app a = 𝟙 _ := by
  simp [monadPowHom_id]

@[simp]
theorem barChangeMap_id (R : RightModule T D) (L : LeftModule A T) (n : ℕ) :
    barChangeMap (D := D) (A := A) (𝟙 T) R L n = 𝟙 _ := by
  ext a
  simp

variable (h : T ⟶ S) (k : S ⟶ U)

theorem barChangeMap_comp_app (R : RightModule U D) (L : LeftModule A U) (n : ℕ) (a : A) :
    (barChangeMap (D := D) (A := A) h ((rightModuleRestrictAlongHom (D := D) k).obj R)
          ((leftModuleRestrictAlongHom (A := A) k).obj L) n ≫
        barChangeMap (D := D) (A := A) k R L n).app a =
      (barChangeMap (D := D) (A := A) (h ≫ k) R L n).app a := by
  simp only [barChangeMap_app, rightModuleRestrictAlongHom_obj_functor,
    leftModuleRestrictAlongHom_obj_functor, NatTrans.comp_app]
  calc
    R.functor.map ((monadPowHom h n).app (L.functor.obj a)) ≫
          R.functor.map ((monadPowHom k n).app (L.functor.obj a))
        = R.functor.map ((monadPowHom h n).app (L.functor.obj a) ≫
            (monadPowHom k n).app (L.functor.obj a)) := by
        rw [← Functor.map_comp]
    _ = R.functor.map ((monadPowHom (h ≫ k) n).app (L.functor.obj a)) := by
        rw [monadPowHom_comp_app]

theorem barChangeMap_comp (R : RightModule U D) (L : LeftModule A U) (n : ℕ) :
    barChangeMap (D := D) (A := A) h ((rightModuleRestrictAlongHom (D := D) k).obj R)
        ((leftModuleRestrictAlongHom (A := A) k).obj L) n ≫
      barChangeMap (D := D) (A := A) k R L n =
    barChangeMap (D := D) (A := A) (h ≫ k) R L n := by
  ext a
  exact barChangeMap_comp_app h k R L n a

end BarChangeMapLaws

section BarDataRestrictIso

universe v₂ v₃ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {A : Type u₃} [Category.{v₃} A]
variable {T S U : Monad C}

/-- Canonical identity restriction iso for bar data, induced by `barDataIso`
and the module `restrictAlongHomIdIso` components whose underlying maps are identities. -/
noncomputable def barDataRestrictIdIso (R : RightModule T D) (L : LeftModule A T) :
    barData T ((rightModuleRestrictAlongHom (D := D) (𝟙 T)).obj R)
      ((leftModuleRestrictAlongHom (A := A) (𝟙 T)).obj L) ≅ barData T R L :=
  barDataIso (RightModule.restrictAlongHomIdIsoComponent R)
    (LeftModule.restrictAlongHomIdIsoComponent L)

@[simp]
theorem barDataRestrictIdIso_hom_app (R : RightModule T D) (L : LeftModule A T) (n : ℕ) :
    (barDataRestrictIdIso (D := D) (A := A) (T := T) R L).hom.app n = 𝟙 _ := by
  ext a
  simp only [barDataRestrictIdIso, barDataIso_hom_app, barMap_app,
    RightModule.restrictAlongHomIdIsoComponent_hom_f]
  have hL : (LeftModule.restrictAlongHomIdIsoComponent L).hom.f.app a = 𝟙 _ := rfl
  rw [hL]
  simp

@[simp]
theorem barDataRestrictIdIso_inv_app (R : RightModule T D) (L : LeftModule A T) (n : ℕ) :
    (barDataRestrictIdIso (D := D) (A := A) (T := T) R L).inv.app n = 𝟙 _ := by
  ext a
  simp only [barDataRestrictIdIso, barDataIso_inv_app, barMap_app,
    RightModule.restrictAlongHomIdIsoComponent_inv_f]
  have hL : (LeftModule.restrictAlongHomIdIsoComponent L).inv.f.app a = 𝟙 _ := rfl
  rw [hL]
  simp

theorem barDataRestrictIdIso_hom_app_app (R : RightModule T D) (L : LeftModule A T)
    (n : ℕ) (a : A) :
    ((barDataRestrictIdIso (D := D) (A := A) (T := T) R L).hom.app n).app a = 𝟙 _ := by
  simp

theorem barDataRestrictIdIso_inv_app_app (R : RightModule T D) (L : LeftModule A T)
    (n : ℕ) (a : A) :
    ((barDataRestrictIdIso (D := D) (A := A) (T := T) R L).inv.app n).app a = 𝟙 _ := by
  simp

/-- Canonical composition restriction iso for bar data, induced by `barDataIso`
and the accepted `restrictAlongHomCompIso` components.
We respect the accepted orientation
`restrictAlongHomCompIso h k : restrict (h ≫ k) ≅ restrict k ⋙ restrict h`,
so the iso goes from the composite restriction to the iterated restriction. -/
noncomputable def barDataRestrictCompIso (h : T ⟶ S) (k : S ⟶ U)
    (R : RightModule U D) (L : LeftModule A U) :
    barData T ((rightModuleRestrictAlongHom (D := D) (h ≫ k)).obj R)
      ((leftModuleRestrictAlongHom (A := A) (h ≫ k)).obj L) ≅
    barData T ((rightModuleRestrictAlongHom (D := D) h).obj
        ((rightModuleRestrictAlongHom (D := D) k).obj R))
      ((leftModuleRestrictAlongHom (A := A) h).obj
        ((leftModuleRestrictAlongHom (A := A) k).obj L)) :=
  barDataIso (RightModule.restrictAlongHomCompIsoComponent R h k)
    (LeftModule.restrictAlongHomCompIsoComponent L h k)

@[simp]
theorem barDataRestrictCompIso_hom_app (h : T ⟶ S) (k : S ⟶ U)
    (R : RightModule U D) (L : LeftModule A U) (n : ℕ) :
    (barDataRestrictCompIso (D := D) (A := A) h k R L).hom.app n = 𝟙 _ := by
  ext a
  simp only [barDataRestrictCompIso, barDataIso_hom_app, barMap_app,
    RightModule.restrictAlongHomCompIsoComponent_hom_f]
  have hL : ((LeftModule.restrictAlongHomCompIsoComponent L h k).hom.f).app a = 𝟙 _ := rfl
  rw [hL]
  simp

@[simp]
theorem barDataRestrictCompIso_inv_app (h : T ⟶ S) (k : S ⟶ U)
    (R : RightModule U D) (L : LeftModule A U) (n : ℕ) :
    (barDataRestrictCompIso (D := D) (A := A) h k R L).inv.app n = 𝟙 _ := by
  ext a
  simp only [barDataRestrictCompIso, barDataIso_inv_app, barMap_app,
    RightModule.restrictAlongHomCompIsoComponent_inv_f]
  have hL : ((LeftModule.restrictAlongHomCompIsoComponent L h k).inv.f).app a = 𝟙 _ := rfl
  rw [hL]
  simp

theorem barDataRestrictCompIso_hom_app_app (h : T ⟶ S) (k : S ⟶ U)
    (R : RightModule U D) (L : LeftModule A U) (n : ℕ) (a : A) :
    ((barDataRestrictCompIso (D := D) (A := A) h k R L).hom.app n).app a = 𝟙 _ := by
  simp

theorem barDataRestrictCompIso_inv_app_app (h : T ⟶ S) (k : S ⟶ U)
    (R : RightModule U D) (L : LeftModule A U) (n : ℕ) (a : A) :
    ((barDataRestrictCompIso (D := D) (A := A) h k R L).inv.app n).app a = 𝟙 _ := by
  simp

end BarDataRestrictIso

section BarChangeDataHomLaws

universe v₂ v₃ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {A : Type u₃} [Category.{v₃} A]
variable {T S U : Monad C}

/-- Data-level identity law: `barChangeDataHom (𝟙 T)` coincides with the
canonical restriction identity iso. No equality of differently restricted module
objects is asserted; we compare via `barDataRestrictIdIso`. -/
theorem barChangeDataHom_id (R : RightModule T D) (L : LeftModule A T) :
    barChangeDataHom (D := D) (A := A) (𝟙 T) R L =
      (barDataRestrictIdIso (D := D) (A := A) (T := T) R L).hom := by
  apply SimplicialObject.Data.Hom.ext
  intro n
  simp only [barChangeDataHom_app, barChangeMap_id,
    barDataRestrictIdIso_hom_app, barData_obj_n]
  rfl

/-- Data-level composition law for same-carrier monad change.

For `h : T ⟶ S`, `k : S ⟶ U`, the composite

`(barDataRestrictCompIso h k R L).hom ≫ barChangeDataHom h (restrict k R) (restrict k L) ≫
  barChangeDataHom k R L`

coincides with `barChangeDataHom (h ≫ k) R L`.

The proof is extensional degreewise and reduces to
`barDataRestrictCompIso_hom_app` (the restriction iso is identity degreewise)
and `barChangeMap_comp`. -/
theorem barChangeDataHom_comp (h : T ⟶ S) (k : S ⟶ U)
    (R : RightModule U D) (L : LeftModule A U) :
    (barDataRestrictCompIso (D := D) (A := A) h k R L).hom ≫
      barChangeDataHom (D := D) (A := A) h ((rightModuleRestrictAlongHom (D := D) k).obj R)
        ((leftModuleRestrictAlongHom (A := A) k).obj L) ≫
      barChangeDataHom (D := D) (A := A) k R L =
    barChangeDataHom (D := D) (A := A) (h ≫ k) R L := by
  apply SimplicialObject.Data.Hom.ext
  intro n
  ext a : 2
  simp only [CategoryTheory.SimplicialObject.comp_app_assoc,
    NatTrans.comp_app,
    barDataRestrictCompIso_hom_app_app, barChangeDataHom_app_app,
    rightModuleRestrictAlongHom_obj_functor, leftModuleRestrictAlongHom_obj_functor,
    barData_obj_obj] at *
  calc
    𝟙 _ ≫ R.functor.map ((monadPowHom h n).app (L.functor.obj a)) ≫
          R.functor.map ((monadPowHom k n).app (L.functor.obj a))
        = R.functor.map ((monadPowHom h n).app (L.functor.obj a)) ≫
          R.functor.map ((monadPowHom k n).app (L.functor.obj a)) := by
        simp
    _ = R.functor.map ((monadPowHom h n).app (L.functor.obj a) ≫
          (monadPowHom k n).app (L.functor.obj a)) := by
        rw [← R.functor.map_comp]
    _ = R.functor.map ((monadPowHom (h ≫ k) n).app (L.functor.obj a)) := by
        rw [monadPowHom_comp_app]

end BarChangeDataHomLaws

section TwoSidedBarRestrictIso

universe v₂ v₃ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {A : Type u₃} [Category.{v₃} A]
variable {T S U : Monad C}

/-- Genuine identity restriction iso, obtained functorially from `barDataRestrictIdIso`
via `Data.toSimplicialFunctor`. -/
noncomputable def twoSidedBarRestrictIdIso (R : RightModule T D) (L : LeftModule A T) :
    twoSidedBar T ((rightModuleRestrictAlongHom (D := D) (𝟙 T)).obj R)
      ((leftModuleRestrictAlongHom (A := A) (𝟙 T)).obj L) ≅
      twoSidedBar T R L :=
  (SimplicialObject.Data.toSimplicialFunctor (C := A ⥤ D)).mapIso
    (barDataRestrictIdIso (D := D) (A := A) (T := T) R L)

/-- Genuine composite-restriction iso, obtained functorially from `barDataRestrictCompIso`.
It preserves the composite-to-iterated orientation:
`restrict (h ≫ k) ≅ restrict k ⋙ restrict h` at the bar level. -/
noncomputable def twoSidedBarRestrictCompIso {S U : Monad C} (h : T ⟶ S) (k : S ⟶ U)
    (R : RightModule U D) (L : LeftModule A U) :
    twoSidedBar T ((rightModuleRestrictAlongHom (D := D) (h ≫ k)).obj R)
      ((leftModuleRestrictAlongHom (A := A) (h ≫ k)).obj L) ≅
    twoSidedBar T ((rightModuleRestrictAlongHom (D := D) h).obj
        ((rightModuleRestrictAlongHom (D := D) k).obj R))
      ((leftModuleRestrictAlongHom (A := A) h).obj
        ((leftModuleRestrictAlongHom (A := A) k).obj L)) :=
  (SimplicialObject.Data.toSimplicialFunctor (C := A ⥤ D)).mapIso
    (barDataRestrictCompIso (D := D) (A := A) h k R L)

@[simp]
theorem twoSidedBarRestrictIdIso_hom_app_op_mk (R : RightModule T D) (L : LeftModule A T)
    (n : ℕ) :
    (twoSidedBarRestrictIdIso (D := D) (A := A) (T := T) R L).hom.app
      (Opposite.op (SimplexCategory.mk n)) = 𝟙 _ := by
  ext a
  exact barDataRestrictIdIso_hom_app_app _ _ n a

@[simp]
theorem twoSidedBarRestrictIdIso_inv_app_op_mk (R : RightModule T D) (L : LeftModule A T)
    (n : ℕ) :
    (twoSidedBarRestrictIdIso (D := D) (A := A) (T := T) R L).inv.app
      (Opposite.op (SimplexCategory.mk n)) = 𝟙 _ := by
  ext a
  exact barDataRestrictIdIso_inv_app_app _ _ n a

theorem twoSidedBarRestrictIdIso_hom_app (R : RightModule T D) (L : LeftModule A T)
    (Δ : SimplexCategoryᵒᵖ) :
    (twoSidedBarRestrictIdIso (D := D) (A := A) (T := T) R L).hom.app Δ = 𝟙 _ := by
  obtain ⟨Δ⟩ := Δ
  exact twoSidedBarRestrictIdIso_hom_app_op_mk (D := D) (A := A) R L Δ.len

theorem twoSidedBarRestrictIdIso_inv_app (R : RightModule T D) (L : LeftModule A T)
    (Δ : SimplexCategoryᵒᵖ) :
    (twoSidedBarRestrictIdIso (D := D) (A := A) (T := T) R L).inv.app Δ = 𝟙 _ := by
  obtain ⟨Δ⟩ := Δ
  exact twoSidedBarRestrictIdIso_inv_app_op_mk (D := D) (A := A) R L Δ.len

theorem twoSidedBarRestrictIdIso_hom_app_app (R : RightModule T D) (L : LeftModule A T)
    (Δ : SimplexCategoryᵒᵖ) (a : A) :
    ((twoSidedBarRestrictIdIso (D := D) (A := A) (T := T) R L).hom.app Δ).app a = 𝟙 _ := by
  obtain ⟨Δ⟩ := Δ
  exact barDataRestrictIdIso_hom_app_app (D := D) (A := A) R L Δ.len a

theorem twoSidedBarRestrictIdIso_inv_app_app (R : RightModule T D) (L : LeftModule A T)
    (Δ : SimplexCategoryᵒᵖ) (a : A) :
    ((twoSidedBarRestrictIdIso (D := D) (A := A) (T := T) R L).inv.app Δ).app a = 𝟙 _ := by
  obtain ⟨Δ⟩ := Δ
  exact barDataRestrictIdIso_inv_app_app (D := D) (A := A) R L Δ.len a

@[simp]
theorem twoSidedBarRestrictCompIso_hom_app_op_mk {S U : Monad C} (h : T ⟶ S) (k : S ⟶ U)
    (R : RightModule U D) (L : LeftModule A U) (n : ℕ) :
    (twoSidedBarRestrictCompIso (D := D) (A := A) h k R L).hom.app
      (Opposite.op (SimplexCategory.mk n)) = 𝟙 _ := by
  ext a
  exact barDataRestrictCompIso_hom_app_app _ _ _ _ n a

@[simp]
theorem twoSidedBarRestrictCompIso_inv_app_op_mk {S U : Monad C} (h : T ⟶ S) (k : S ⟶ U)
    (R : RightModule U D) (L : LeftModule A U) (n : ℕ) :
    (twoSidedBarRestrictCompIso (D := D) (A := A) h k R L).inv.app
      (Opposite.op (SimplexCategory.mk n)) = 𝟙 _ := by
  ext a
  exact barDataRestrictCompIso_inv_app_app _ _ _ _ n a

theorem twoSidedBarRestrictCompIso_hom_app {S U : Monad C} (h : T ⟶ S) (k : S ⟶ U)
    (R : RightModule U D) (L : LeftModule A U) (Δ : SimplexCategoryᵒᵖ) :
    (twoSidedBarRestrictCompIso (D := D) (A := A) h k R L).hom.app Δ = 𝟙 _ := by
  obtain ⟨Δ⟩ := Δ
  exact twoSidedBarRestrictCompIso_hom_app_op_mk (D := D) (A := A) h k R L Δ.len

theorem twoSidedBarRestrictCompIso_inv_app {S U : Monad C} (h : T ⟶ S) (k : S ⟶ U)
    (R : RightModule U D) (L : LeftModule A U) (Δ : SimplexCategoryᵒᵖ) :
    (twoSidedBarRestrictCompIso (D := D) (A := A) h k R L).inv.app Δ = 𝟙 _ := by
  obtain ⟨Δ⟩ := Δ
  exact twoSidedBarRestrictCompIso_inv_app_op_mk (D := D) (A := A) h k R L Δ.len

theorem twoSidedBarRestrictCompIso_hom_app_app {S U : Monad C} (h : T ⟶ S) (k : S ⟶ U)
    (R : RightModule U D) (L : LeftModule A U) (Δ : SimplexCategoryᵒᵖ) (a : A) :
    ((twoSidedBarRestrictCompIso (D := D) (A := A) h k R L).hom.app Δ).app a = 𝟙 _ := by
  obtain ⟨Δ⟩ := Δ
  exact barDataRestrictCompIso_hom_app_app (D := D) (A := A) h k R L Δ.len a

theorem twoSidedBarRestrictCompIso_inv_app_app {S U : Monad C} (h : T ⟶ S) (k : S ⟶ U)
    (R : RightModule U D) (L : LeftModule A U) (Δ : SimplexCategoryᵒᵖ) (a : A) :
    ((twoSidedBarRestrictCompIso (D := D) (A := A) h k R L).inv.app Δ).app a = 𝟙 _ := by
  obtain ⟨Δ⟩ := Δ
  exact barDataRestrictCompIso_inv_app_app (D := D) (A := A) h k R L Δ.len a

end TwoSidedBarRestrictIso

section BarChangeHomLaws

universe v₂ v₃ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {A : Type u₃} [Category.{v₃} A]
variable {T S U : Monad C}

/-- Genuine identity law: `barChangeHom (𝟙 T)` equals the identity-restriction iso hom.

Derived functorially from `barChangeDataHom_id` via `Data.toSimplicialFunctor`. -/
theorem barChangeHom_id (R : RightModule T D) (L : LeftModule A T) :
    barChangeHom (D := D) (A := A) (𝟙 T) R L =
      (twoSidedBarRestrictIdIso (D := D) (A := A) (T := T) R L).hom := by
  change SimplicialObject.Data.toSimplicialNatTrans
      (barChangeDataHom (D := D) (A := A) (𝟙 T) R L) =
    (twoSidedBarRestrictIdIso (D := D) (A := A) (T := T) R L).hom
  change (SimplicialObject.Data.toSimplicialFunctor (C := A ⥤ D)).map
      (barChangeDataHom (D := D) (A := A) (𝟙 T) R L) =
    (twoSidedBarRestrictIdIso (D := D) (A := A) (T := T) R L).hom
  have h_functor_hom : (twoSidedBarRestrictIdIso (D := D) (A := A) (T := T) R L).hom =
      (SimplicialObject.Data.toSimplicialFunctor (C := A ⥤ D)).map
        (barDataRestrictIdIso (D := D) (A := A) (T := T) R L).hom := rfl
  rw [h_functor_hom, barChangeDataHom_id]

/-- Genuine composition law: composite-restriction iso hom followed by two genuine
bar-change maps for `h` and `k` equals the genuine bar-change map for `h ≫ k`.

Derived functorially from `barChangeDataHom_comp` via `Data.toSimplicialFunctor`
and `Functor.map_comp`. -/
theorem barChangeHom_comp (h : T ⟶ S) (k : S ⟶ U)
    (R : RightModule U D) (L : LeftModule A U) :
    (twoSidedBarRestrictCompIso (D := D) (A := A) h k R L).hom ≫
      barChangeHom (D := D) (A := A) h
        ((rightModuleRestrictAlongHom (D := D) k).obj R)
        ((leftModuleRestrictAlongHom (A := A) k).obj L) ≫
      barChangeHom (D := D) (A := A) k R L =
    barChangeHom (D := D) (A := A) (h ≫ k) R L := by
  change (SimplicialObject.Data.toSimplicialFunctor (C := A ⥤ D)).map
      (barDataRestrictCompIso (D := D) (A := A) h k R L).hom ≫
    SimplicialObject.Data.toSimplicialNatTrans
      (barChangeDataHom (D := D) (A := A) h
        ((rightModuleRestrictAlongHom (D := D) k).obj R)
        ((leftModuleRestrictAlongHom (A := A) k).obj L)) ≫
    SimplicialObject.Data.toSimplicialNatTrans
      (barChangeDataHom (D := D) (A := A) k R L) =
    SimplicialObject.Data.toSimplicialNatTrans
      (barChangeDataHom (D := D) (A := A) (h ≫ k) R L)
  change (SimplicialObject.Data.toSimplicialFunctor (C := A ⥤ D)).map
      (barDataRestrictCompIso (D := D) (A := A) h k R L).hom ≫
    (SimplicialObject.Data.toSimplicialFunctor (C := A ⥤ D)).map
      (barChangeDataHom (D := D) (A := A) h
        ((rightModuleRestrictAlongHom (D := D) k).obj R)
        ((leftModuleRestrictAlongHom (A := A) k).obj L)) ≫
    (SimplicialObject.Data.toSimplicialFunctor (C := A ⥤ D)).map
      (barChangeDataHom (D := D) (A := A) k R L) =
    (SimplicialObject.Data.toSimplicialFunctor (C := A ⥤ D)).map
      (barChangeDataHom (D := D) (A := A) (h ≫ k) R L)
  calc
    (SimplicialObject.Data.toSimplicialFunctor (C := A ⥤ D)).map
        (barDataRestrictCompIso (D := D) (A := A) h k R L).hom ≫
    (SimplicialObject.Data.toSimplicialFunctor (C := A ⥤ D)).map
        (barChangeDataHom (D := D) (A := A) h
          ((rightModuleRestrictAlongHom (D := D) k).obj R)
          ((leftModuleRestrictAlongHom (A := A) k).obj L)) ≫
    (SimplicialObject.Data.toSimplicialFunctor (C := A ⥤ D)).map
        (barChangeDataHom (D := D) (A := A) k R L) =
    (SimplicialObject.Data.toSimplicialFunctor (C := A ⥤ D)).map
        ((barDataRestrictCompIso (D := D) (A := A) h k R L).hom ≫
          barChangeDataHom (D := D) (A := A) h
            ((rightModuleRestrictAlongHom (D := D) k).obj R)
            ((leftModuleRestrictAlongHom (A := A) k).obj L) ≫
          barChangeDataHom (D := D) (A := A) k R L) := by
      rw [Functor.map_comp, Functor.map_comp]
    _ = (SimplicialObject.Data.toSimplicialFunctor (C := A ⥤ D)).map
        (barChangeDataHom (D := D) (A := A) (h ≫ k) R L) := by
      rw [barChangeDataHom_comp]

end BarChangeHomLaws

section MixedNaturality

universe v₂ v₃ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {A : Type u₃} [Category.{v₃} A]
variable {T S : Monad C}

/-- Degreewise mixed naturality between restricted `barMap` and `barChangeMap`.

For `h : T ⟶ S`, `fR : R ⟶ R'`, `fL : L ⟶ L'`, the restricted bar map followed
by the monad-change map equals the monad-change map followed by the bar map.
Both module variables are covariant. Same carrier only. -/
theorem barChangeMap_naturality (h : T ⟶ S)
    {R R' : RightModule S D} {L L' : LeftModule A S}
    (fR : R ⟶ R') (fL : L ⟶ L') (n : ℕ) :
    barMap ((rightModuleRestrictAlongHom (D := D) h).map fR)
      ((leftModuleRestrictAlongHom (A := A) h).map fL) n ≫
      barChangeMap (D := D) (A := A) h R' L' n =
    barChangeMap (D := D) (A := A) h R L n ≫ barMap fR fL n := by
  ext a
  simp only [barMap_app, barChangeMap_app, NatTrans.comp_app,
    rightModuleRestrictAlongHom_obj_functor, leftModuleRestrictAlongHom_obj_functor]
  change (R.functor.map ((monadPow T n).map (fL.f.app a)) ≫
      fR.f.app ((monadPow T n).obj (L'.functor.obj a))) ≫
      R'.functor.map ((monadPowHom h n).app (L'.functor.obj a)) =
    R.functor.map ((monadPowHom h n).app (L.functor.obj a)) ≫
      (R.functor.map ((monadPow S n).map (fL.f.app a)) ≫
        fR.f.app ((monadPow S n).obj (L'.functor.obj a)))
  have h_tail : fR.f.app ((monadPow T n).obj (L'.functor.obj a)) ≫
      R'.functor.map ((monadPowHom h n).app (L'.functor.obj a)) =
      R.functor.map ((monadPowHom h n).app (L'.functor.obj a)) ≫
        fR.f.app ((monadPow S n).obj (L'.functor.obj a)) :=
    (fR.f.naturality ((monadPowHom h n).app (L'.functor.obj a))).symm
  have h_pow : (monadPow T n).map (fL.f.app a) ≫
      (monadPowHom h n).app (L'.functor.obj a) =
      (monadPowHom h n).app (L.functor.obj a) ≫
        (monadPow S n).map (fL.f.app a) :=
    (monadPowHom h n).naturality (fL.f.app a)
  calc
    (R.functor.map ((monadPow T n).map (fL.f.app a)) ≫
        fR.f.app ((monadPow T n).obj (L'.functor.obj a))) ≫
        R'.functor.map ((monadPowHom h n).app (L'.functor.obj a))
        = R.functor.map ((monadPow T n).map (fL.f.app a)) ≫
          (fR.f.app ((monadPow T n).obj (L'.functor.obj a)) ≫
            R'.functor.map ((monadPowHom h n).app (L'.functor.obj a))) := by
          rw [Category.assoc]
    _ = R.functor.map ((monadPow T n).map (fL.f.app a)) ≫
          (R.functor.map ((monadPowHom h n).app (L'.functor.obj a)) ≫
            fR.f.app ((monadPow S n).obj (L'.functor.obj a))) := by
          rw [h_tail]
    _ = (R.functor.map ((monadPow T n).map (fL.f.app a)) ≫
          R.functor.map ((monadPowHom h n).app (L'.functor.obj a))) ≫
          fR.f.app ((monadPow S n).obj (L'.functor.obj a)) := by
          rw [← Category.assoc]
    _ = R.functor.map ((monadPow T n).map (fL.f.app a) ≫
          (monadPowHom h n).app (L'.functor.obj a)) ≫
          fR.f.app ((monadPow S n).obj (L'.functor.obj a)) := by
          rw [← R.functor.map_comp]
    _ = R.functor.map ((monadPowHom h n).app (L.functor.obj a) ≫
          (monadPow S n).map (fL.f.app a)) ≫
          fR.f.app ((monadPow S n).obj (L'.functor.obj a)) := by
          rw [h_pow]
    _ = (R.functor.map ((monadPowHom h n).app (L.functor.obj a)) ≫
          R.functor.map ((monadPow S n).map (fL.f.app a))) ≫
          fR.f.app ((monadPow S n).obj (L'.functor.obj a)) := by
          rw [R.functor.map_comp]
    _ = R.functor.map ((monadPowHom h n).app (L.functor.obj a)) ≫
          (R.functor.map ((monadPow S n).map (fL.f.app a)) ≫
            fR.f.app ((monadPow S n).obj (L'.functor.obj a))) := by
          rw [Category.assoc]

/-- Genuine mixed naturality for `barChangeHom`. Follows degreewise from
`barChangeMap_naturality`. Same carrier only. -/
theorem barChangeHom_naturality (h : T ⟶ S)
    {R R' : RightModule S D} {L L' : LeftModule A S}
    (fR : R ⟶ R') (fL : L ⟶ L') :
    twoSidedBarHom ((rightModuleRestrictAlongHom (D := D) h).map fR)
      ((leftModuleRestrictAlongHom (A := A) h).map fL) ≫
      barChangeHom (D := D) (A := A) h R' L' =
    barChangeHom (D := D) (A := A) h R L ≫ twoSidedBarHom fR fL := by
  ext Δ a
  simp only [NatTrans.comp_app, twoSidedBarHom_app, barChangeHom_app]
  exact NatTrans.congr_app
    (barChangeMap_naturality (D := D) (A := A) h fR fL (Opposite.unop Δ).len) a

/-- Fixed-monad-hom natural transformation packaging `barChangeHom`.

For fixed `h : T ⟶ S`, the family `barChangeHom h R L` is natural in `(R, L)`
via Mathlib's `Functor.prod` restriction. Both module variables are covariant.
Same carrier only; no carrier-change, outer-whiskering, evaluation,
balanced-tensor, or operadic API. -/
noncomputable def barChangeNatTrans (h : T ⟶ S) :
    (rightModuleRestrictAlongHom (D := D) h).prod
      (leftModuleRestrictAlongHom (A := A) h) ⋙
      twoSidedBarFunctor T ⟶ twoSidedBarFunctor S where
  app p := barChangeHom (D := D) (A := A) h p.1 p.2
  naturality := fun p q f => by
    obtain ⟨R, L⟩ := p
    obtain ⟨R', L'⟩ := q
    obtain ⟨fR, fL⟩ := f
    change twoSidedBarHom ((rightModuleRestrictAlongHom (D := D) h).map fR)
        ((leftModuleRestrictAlongHom (A := A) h).map fL) ≫
        barChangeHom (D := D) (A := A) h R' L' =
      barChangeHom (D := D) (A := A) h R L ≫ twoSidedBarHom fR fL
    exact barChangeHom_naturality (D := D) (A := A) h fR fL

end MixedNaturality

section BarChangeNatTransLaws

universe v₂ v₃ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {A : Type u₃} [Category.{v₃} A]
variable {T S U : Monad C}

/-- NatTrans-level identity coherence for `barChangeNatTrans`.

At `𝟙 T`, the packaged natural transformation acts as the identity-restriction
iso. This is `barChangeHom_id` at each component; unfolding the `app` field of
`barChangeNatTrans` is definitional, so no new naturality argument is needed. -/
@[simp]
theorem barChangeNatTrans_id_app (p : RightModule T D × LeftModule A T) :
    (barChangeNatTrans (D := D) (A := A) (𝟙 T)).app p =
      (twoSidedBarRestrictIdIso (D := D) (A := A) p.1 p.2).hom :=
  barChangeHom_id p.1 p.2

/-- NatTrans-level composition coherence for `barChangeNatTrans`.

At `h ≫ k`, the packaged natural transformation factors through the
composite-restriction iso followed by the two packaged maps. This is
`barChangeHom_comp` at each component; no category of monads is introduced. -/
@[simp]
theorem barChangeNatTrans_comp_app (h : T ⟶ S) (k : S ⟶ U)
    (p : RightModule U D × LeftModule A U) :
    (barChangeNatTrans (D := D) (A := A) (h ≫ k)).app p =
      (twoSidedBarRestrictCompIso (D := D) (A := A) h k p.1 p.2).hom ≫
        (barChangeNatTrans (D := D) (A := A) h).app
          ((rightModuleRestrictAlongHom (D := D) k).obj p.1,
            (leftModuleRestrictAlongHom (A := A) k).obj p.2) ≫
        (barChangeNatTrans (D := D) (A := A) k).app p :=
  (barChangeHom_comp h k p.1 p.2).symm

end BarChangeNatTransLaws

end Monad
end CategoryTheory
