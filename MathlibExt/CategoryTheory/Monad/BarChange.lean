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
# Changing the monad in a two-sided bar

Let T,S be monads on a category C and h : T → S a monad morphism. The natural maps h^n : T^n →
S^n commute with unit insertions and multiplication of adjacent factors. For a right S-module
R : C → D and a left S-module L : A → C, restricting both actions along h gives a simplicial
map B(h*R,T,h*L) → B(R,S,L). In degree n at a ∈ A it is R(h^n_{L(a)}).

The bar maps preserve identity and composition through the canonical isomorphisms for identity
and composite module restriction. They are natural, covariantly in both module variables. The
three categories may have independent object and morphism universes; T and S act on the same
base category C.

The functor on bar triples and its functor-valued left input are described in J. P. May,
*The Geometry of Iterated Loop Spaces*, Lecture Notes in Mathematics 271, Springer, 1972,
Chapter 9, Construction 9.6 and Remark 9.12, <https://doi.org/10.1007/BFb0067491>.
-/

@[expose] public section

namespace CategoryTheory
namespace Monad

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C]

/-- Let C be a category and h : T → S a monad morphism on C. Define natural transformations h^n :
T^n → S^n recursively by h^0=id and h^{n+1}=h horizontally composed with h^n. Here T^n and S^n
are monadPow at n. This is the comparison obtained by applying h to every one of the n monad
factors. -/
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

/-- Let h : T → S be a monad morphism on a category C, n ∈ ℕ, and X ∈ C. The power comparison
satisfies h^{n+1}_X = h^n_{T(X)} ≫ S^n(h_X). The first map compares the outer n factors at
T(X), and the second applies S^n to the innermost component h_X. -/
@[simp]
lemma monadPowHom_succ_app {T S : Monad C} (h : T ⟶ S) (n : ℕ) (X : C) :
    (monadPowHom h (n + 1)).app X =
      (monadPowHom h n).app (T.obj X) ≫ (monadPow S n).map (h.app X) := by
  have hdef : (monadPowHom h (n + 1)).app X =
      (h.toNatTrans ◫ monadPowHom h n).app X := rfl
  rw [hdef, NatTrans.hcomp_app]

/-- For a monad morphism h : T → S on C, n ∈ ℕ, and X ∈ C, h^{n+1}_X = T^n(h_X) ≫ h^n_{S(X)}. This
is the naturality form of the successor comparison, applying the source power to h_X before
comparing the n remaining powers. -/
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

/-- For a monad T on a category C and n ∈ ℕ, the power comparison induced by the identity monad
morphism equals id_{T^n}. Thus monadPowHom(𝟙_T,n) is the identity natural transformation of
monadPow T n. -/
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

/-- Let h : T → S and k : S → U be monad morphisms on the same category C. For every n ∈ ℕ, (h ≫
k)^n = h^n ≫ k^n as natural transformations T^n → U^n. The equality compares the n-fold power
map of the composite with the composite of the two power comparisons. -/
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
        (monadPowHom h (n + 1)).naturality (T.η.app X)
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
        (monadPowHom h n).naturality (T.μ.app X)
      have natPowTmap : (monadPow T n).map (T.map (h.app X)) ≫
          (monadPowHom h n).app (T.obj (S.obj X)) =
          (monadPowHom h n).app (T.obj (T.obj X)) ≫
            (monadPow S n).map (T.map (h.app X)) :=
        (monadPowHom h n).naturality (T.map (h.app X))
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

/-- A monad morphism induces the degreewise comparison of two-sided bars.

For `h : T ⟶ S`, a right `S`-module `R : C ⥤ D` and a left `S`-module `L : A ⥤ C`, the map
in degree `n` is the double whiskering of `monadPowHom h n`. Its component at `a` is
`R(h^n_{L(a)})`, from the bar of the restricted modules to the original bar. -/
noncomputable def barChangeMap {T S : Monad C} (h : T ⟶ S) (R : RightModule S D)
    (L : LeftModule A S) (n : ℕ) :
    barObj T ((rightModuleRestrictAlongHom (D := D) h).obj R)
      ((leftModuleRestrictAlongHom (A := A) h).obj L) n ⟶
      barObj S R L n :=
  Functor.whiskerRight
    (Functor.whiskerLeft L.functor (monadPowHom h n)) R.functor

@[simp]
lemma barChangeMap_app {T S : Monad C} {D : Type u₂} [Category.{v₂} D] {A : Type u₃}
    [Category.{v₃} A] (h : T ⟶ S) (R : RightModule S D) (L : LeftModule A S) (n : ℕ)
    (a : A) :
    (barChangeMap (D := D) (A := A) h R L n).app a =
      R.functor.map ((monadPowHom h n).app (L.functor.obj a)) := rfl

/--
For a monad morphism h : T → S on C, a right S-module R : C → D, and a left S-module L : A →
C, the maps c_n=R(h^n_{L(-)}) commute with every bar degeneracy. Thus c_n ≫ s_i^S = s_i^T ≫
c_{n+1} for i ∈ Fin(n+1), where the source actions are restricted along h and s_i inserts a
monad unit.
-/

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

/--
For h : T → S and S-modules R,L, the degreewise bar-change maps commute with each middle face.
These faces multiply two adjacent monad factors, and the identity is the compatibility of h^n
with the multiplication insertions of T and S.
-/

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

/--
Let h : T → S be a monad morphism and R : C → D a right S-module. For n ∈ ℕ and X ∈ C,
R(h^{n+1}_X) followed by the iterated S-action equals the iterated action of the restricted
T-module followed by R(h^n_X). This is the right-action compatibility used at the first bar
face.
-/

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

/--
The bar-change map commutes with the right endpoint face d_0. For every n, c_{n+1} ≫ d_0^S =
d_0^T ≫ c_n, where the source right-module action is restricted along the monad morphism and c
is the degreewise map induced by h^n.
-/

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

/--
The bar-change map commutes with the left endpoint face d_{n+1}. For every n, c_{n+1} ≫
d_{n+1}^S = d_{n+1}^T ≫ c_n, using the left S-module action and its restriction along h : T →
S.
-/

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

/--
For a monad morphism h : T → S and right and left S-modules R,L, the degreewise change maps
satisfy c_{n+1} ≫ d_j^S = d_j^T ≫ c_n for every n ∈ ℕ and j ∈ Fin(n+2). This includes the two
endpoint faces and every middle multiplication face.
-/

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

/--
The degree maps c_n=R(h^n_{L(-)}) and their face and degeneracy equations define a morphism of
two-sided bar simplicial data from the T-bar of the restricted modules to the S-bar of R,L.
Passing to simplicial objects gives the same degreewise maps.
-/

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

/-- Let C,A,D be categories, h : T → S a monad morphism on C, R : C → D a right S-module, and L :
A → C a left S-module. Restrict their actions along h to obtain T-modules h*R,h*L. There is a
simplicial morphism B(h*R,T,h*L) → B(R,S,L) in A ⥤ D, with degree-n component at a given by
R(h^n_{L(a)}). It commutes with all unit-insertion degeneracies and with the right-action,
middle-multiplication, and left-action faces. -/
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

@[simp]
theorem barChangeHom_app (h : T ⟶ S) (R : RightModule S D)
    (L : LeftModule A S) (Δ : SimplexCategoryᵒᵖ) :
    (barChangeHom (D := D) (A := A) h R L).app Δ =
      barChangeMap (D := D) (A := A) h R L (Opposite.unop Δ).len := by
  obtain ⟨Δ⟩ := Δ
  rfl

@[simp]
theorem barChangeHom_app_app_op_mk (h : T ⟶ S) (R : RightModule S D)
    (L : LeftModule A S) (n : ℕ) (a : A) :
    ((barChangeHom (D := D) (A := A) h R L).app (Opposite.op (SimplexCategory.mk n))).app a =
      R.functor.map ((monadPowHom h n).app (L.functor.obj a)) :=
  rfl

@[simp]
theorem barChangeHom_app_app (h : T ⟶ S) (R : RightModule S D)
    (L : LeftModule A S) (Δ : SimplexCategoryᵒᵖ) (a : A) :
    ((barChangeHom (D := D) (A := A) h R L).app Δ).app a =
      R.functor.map ((monadPowHom h (Opposite.unop Δ).len).app (L.functor.obj a)) := by
  obtain ⟨Δ⟩ := Δ
  rfl

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

/-- Let T be a monad on C, R : C → D a right T-module, and L : A → C a left T-module. The bar data
of their restrictions along id_T are canonically isomorphic to B(R,T,L). The comparison uses
the module identity-restriction isomorphisms and is the identity on each degree object
R(T^n(L(a))), preserving faces and degeneracies. -/
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

/-- Let h : T → S and k : S → U be monad morphisms on C, and R : C → D and L : A → C be U-modules.
The T-bar data of the restrictions along h≫k are canonically isomorphic to the T-bar data
obtained by restricting first along k and then along h. The isomorphism is oriented from
composite restriction to iterated restriction and uses identity maps on the degree carriers
R(T^n(L(a))). -/
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

/-- For a monad T on C, a right T-module R : C → D, and a left T-module L : A → C, the bar-data
map induced by id_T equals the forward map of barDataRestrictIdIso(R,L). Its source is the
T-bar of the identity-restricted modules and its target is the T-bar of R,L. -/
theorem barChangeDataHom_id (R : RightModule T D) (L : LeftModule A T) :
    barChangeDataHom (D := D) (A := A) (𝟙 T) R L =
      (barDataRestrictIdIso (D := D) (A := A) (T := T) R L).hom := by
  apply SimplicialObject.Data.Hom.ext
  intro n
  simp only [barChangeDataHom_app, barChangeMap_id,
    barDataRestrictIdIso_hom_app, barData_obj_n]
  rfl

/-- Let h : T → S, k : S → U be monad morphisms on C and R,L be right and left U-modules with
functors C → D and A → C. Let e identify the T-bar of the composite restrictions with the
T-bar of h*(k*R),h*(k*L). Then e.hom ≫ c_h(k*R,k*L) ≫ c_k(R,L) = c_{h≫k}(R,L) as bar-data
morphisms. Each c is the power-induced bar-change map. -/
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

/-- For a monad T on C and T-modules R : C → D and L : A → C, the two-sided bar of the modules
restricted along id_T is canonically isomorphic to B(R,T,L) as a simplicial object of A ⥤ D.
The isomorphism is induced by the identity-restriction module comparisons and has identity
degree components. -/
noncomputable def twoSidedBarRestrictIdIso (R : RightModule T D) (L : LeftModule A T) :
    twoSidedBar T ((rightModuleRestrictAlongHom (D := D) (𝟙 T)).obj R)
      ((leftModuleRestrictAlongHom (A := A) (𝟙 T)).obj L) ≅
      twoSidedBar T R L :=
  twoSidedBarIso (RightModule.restrictAlongHomIdIsoComponent R)
    (LeftModule.restrictAlongHomIdIsoComponent L)

/-- Let h : T → S and k : S → U be monad morphisms on C, and R : C → D and L : A → C be U-modules.
There is a simplicial isomorphism from the T-bar of the modules restricted along h≫k to the
T-bar of the modules restricted first along k and then along h. It retains the
composite-to-iterated direction and has identity components on the common degree objects. -/
noncomputable def twoSidedBarRestrictCompIso {S U : Monad C} (h : T ⟶ S) (k : S ⟶ U)
    (R : RightModule U D) (L : LeftModule A U) :
    twoSidedBar T ((rightModuleRestrictAlongHom (D := D) (h ≫ k)).obj R)
      ((leftModuleRestrictAlongHom (A := A) (h ≫ k)).obj L) ≅
    twoSidedBar T ((rightModuleRestrictAlongHom (D := D) h).obj
        ((rightModuleRestrictAlongHom (D := D) k).obj R))
      ((leftModuleRestrictAlongHom (A := A) h).obj
        ((leftModuleRestrictAlongHom (A := A) k).obj L)) :=
  twoSidedBarIso (RightModule.restrictAlongHomCompIsoComponent R h k)
    (LeftModule.restrictAlongHomCompIsoComponent L h k)

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

/-- Let T be a monad on C, R : C → D a right T-module, and L : A → C a left T-module. The
simplicial bar-change map induced by id_T equals the forward identity-restriction isomorphism
from B(id_T*R,T,id_T*L) to B(R,T,L). This is an equality of simplicial morphisms. -/
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

/-- Let h : T → S, k : S → U be monad morphisms on C, and R,L be right and left U-modules. If e is
the simplicial comparison from composite restriction to iterated restriction, then e.hom ≫
c_h(k*R,k*L) ≫ c_k(R,L) = c_{h≫k}(R,L). The maps are simplicial two-sided bar maps with values
in A ⥤ D, where L : A → C and R : C → D. -/
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

/-- Let h : T → S be a monad morphism on C, R,R′ right S-modules in C → D, and L,L′ left S-modules
in A → C. For module maps f_R : R → R′ and f_L : L → L′ and n ∈ ℕ, the T-bar map of their
restrictions followed by c_h(R′,L′)_n equals c_h(R,L)_n followed by the S-bar map of f_R,f_L.
Thus the power-induced degree map is covariantly natural in both module variables. -/
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

/-- Let h : T → S be a monad morphism on C, f_R : R → R′ a right S-module map, and f_L : L → L′ a
left S-module map, with underlying functors C → D and A → C. The simplicial equation is
B_T(h*f_R,h*f_L) ≫ c_h(R′,L′) = c_h(R,L) ≫ B_S(f_R,f_L). Both module variables are covariant
and the monads share the base category C. -/
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

/-- Let h : T → S be a monad morphism on C and let A,D be categories. Restricting right S-modules
C → D and left S-modules A → C along h, then taking the T-bar, defines a functor on their
product category. The maps c_h(R,L) form a natural transformation from this functor to the
S-bar functor. Its component at (R,L) is the simplicial bar-change map with degree formula
R(h^n_{L(-)}). -/
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

/-- Let T be a monad on C and p=(R,L), with R : C → D a right T-module and L : A → C a left
T-module. The component at p of the bar-change natural transformation for id_T equals the
forward map of the simplicial identity-restriction isomorphism. This identifies the component
from the bar of id_T-restricted modules to B(R,T,L). -/
@[simp]
theorem barChangeNatTrans_id_app (p : RightModule T D × LeftModule A T) :
    (barChangeNatTrans (D := D) (A := A) (𝟙 T)).app p =
      (twoSidedBarRestrictIdIso (D := D) (A := A) p.1 p.2).hom :=
  barChangeHom_id p.1 p.2

/-- Let h : T → S, k : S → U be monad morphisms on C and p=(R,L) a pair of right and left
U-modules with functors C → D and A → C. The component θ_{h≫k}(p) equals e_p.hom ≫
θ_h(k*R,k*L) ≫ θ_k(p), where e_p is the simplicial isomorphism from composite restriction to
iterated restriction. Here θ denotes the bar-change natural transformation. -/
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
