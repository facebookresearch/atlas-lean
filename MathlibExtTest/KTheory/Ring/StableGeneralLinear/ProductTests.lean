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

public import MathlibExt.KTheory.Ring.StableGeneralLinear.Product

/-! Public-API tests for finite and stable general-linear product equivalences. -/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v w

namespace MathlibExtTest.KTheory.Ring.StableGeneralLinear.ProductTests

open AlgebraicKTheory

variable {R S R' S' : Type u}
variable [Semiring R] [Semiring S] [Semiring R'] [Semiring S']

section SeparateUniverses

variable {T T' : Type v}
variable [Semiring T] [Semiring T']
variable {n : Type w} [Fintype n] [DecidableEq n]

example : Matrix n n (R × T) ≃+* Matrix n n R × Matrix n n T :=
  Matrix.prodRingEquiv n R T

example (A : Matrix n n (R × T)) :
    Matrix.prodRingEquiv n R T A =
      (A.map (RingHom.fst R T), A.map (RingHom.snd R T)) := by
  ext <;> simp

example (A : Matrix n n R × Matrix n n T) (i j : n) :
    (Matrix.prodRingEquiv n R T).symm A i j =
      (A.1 i j, A.2 i j) := by
  simp

example : Matrix.GeneralLinearGroup n (R × T) ≃*
    Matrix.GeneralLinearGroup n R × Matrix.GeneralLinearGroup n T :=
  Matrix.GeneralLinearGroup.prodSemiringEquiv (R := R) (S := T) n

example (f : R →+* R') (g : T →+* T')
    (A : Matrix.GeneralLinearGroup n (R × T)) :
    Matrix.GeneralLinearGroup.prodSemiringEquiv (R := R') (S := T') n
        (Matrix.GeneralLinearGroup.mapRingHom (f.prodMap g) A) =
      (Matrix.GeneralLinearGroup.mapRingHom f
          (Matrix.GeneralLinearGroup.prodSemiringEquiv (R := R) (S := T) n A).1,
        Matrix.GeneralLinearGroup.mapRingHom g
          (Matrix.GeneralLinearGroup.prodSemiringEquiv (R := R) (S := T) n A).2) := by
  exact Matrix.GeneralLinearGroup.prodSemiringEquiv_mapRingHom n f g A

end SeparateUniverses

example {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix.GeneralLinearGroup n (R × S)) :
    Matrix.GeneralLinearGroup.prodSemiringEquiv (R := R) (S := S) n A =
      (Matrix.GeneralLinearGroup.mapRingHom (RingHom.fst R S) A,
        Matrix.GeneralLinearGroup.mapRingHom (RingHom.snd R S) A) := by
  ext <;> simp

example {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix.GeneralLinearGroup n R)
    (B : Matrix.GeneralLinearGroup n S) (i j : n) :
    ((↑((Matrix.GeneralLinearGroup.prodSemiringEquiv
        (R := R) (S := S) n).symm (A, B)) : Matrix n n (R × S)) i j) =
      ((A : Matrix n n R) i j, (B : Matrix n n S) i j) := by
  simp

example {n m : ℕ} (f : n ⟶ m)
    (A : Matrix.GeneralLinearGroup (Fin n) (R × S)) :
    Matrix.GeneralLinearGroup.prodSemiringEquiv (R := R) (S := S) (Fin m)
        ((finiteGLDiagram.obj (SemiRingCat.of (R × S))).map f A) =
      ((finiteGLDiagram.obj (SemiRingCat.of R)).map f
          (Matrix.GeneralLinearGroup.prodSemiringEquiv (R := R) (S := S) (Fin n) A).1,
        (finiteGLDiagram.obj (SemiRingCat.of S)).map f
          (Matrix.GeneralLinearGroup.prodSemiringEquiv (R := R) (S := S) (Fin n) A).2) :=
  StableGL.finite_prodEquiv_map f A

example {n : ℕ} (A : Matrix.GeneralLinearGroup (Fin n) (R × S)) :
    StableGL.prodEquiv R S (StableGL.of A) =
      (StableGL.of
          (Matrix.GeneralLinearGroup.prodSemiringEquiv (R := R) (S := S) (Fin n) A).1,
        StableGL.of
          (Matrix.GeneralLinearGroup.prodSemiringEquiv (R := R) (S := S) (Fin n) A).2) := by
  exact StableGL.prodEquiv_of A

example {n : ℕ} (A : Matrix.GeneralLinearGroup (Fin n) R)
    (B : Matrix.GeneralLinearGroup (Fin n) S) :
    (StableGL.prodEquiv R S).symm (StableGL.of A, StableGL.of B) =
      StableGL.of ((Matrix.GeneralLinearGroup.prodSemiringEquiv
        (R := R) (S := S) (Fin n)).symm (A, B)) := by
  exact StableGL.prodEquiv_symm_of_pair A B

example (f : R →+* R') (g : S →+* S') (x : StableGL (R × S)) :
    StableGL.prodEquiv R' S'
        (StableGL.functor.map (SemiRingCat.ofHom (f.prodMap g)) x) =
      (StableGL.functor.map (SemiRingCat.ofHom f) (StableGL.prodEquiv R S x).1,
        StableGL.functor.map (SemiRingCat.ofHom g) (StableGL.prodEquiv R S x).2) :=
  StableGL.prodEquiv_mapRingHom f g x

example (A : Matrix.GeneralLinearGroup (Fin 0) (R × S)) :
    StableGL.prodEquiv R S (StableGL.of A) =
      (StableGL.of
          (Matrix.GeneralLinearGroup.prodSemiringEquiv (R := R) (S := S) (Fin 0) A).1,
        StableGL.of
          (Matrix.GeneralLinearGroup.prodSemiringEquiv (R := R) (S := S) (Fin 0) A).2) := by
  exact StableGL.prodEquiv_of A

-- The stable construction is genuinely semiring-generic; no additive
-- inverses are used in its formulas or pair-map naturality.
example : StableGL (ℕ × ℕ) ≃* StableGL ℕ × StableGL ℕ :=
  StableGL.prodEquiv ℕ ℕ

example {n : ℕ} (A : Matrix.GeneralLinearGroup (Fin n) (ℕ × ℕ)) :
    StableGL.prodEquiv ℕ ℕ (StableGL.of A) =
      (StableGL.of
          (Matrix.GeneralLinearGroup.prodSemiringEquiv (R := ℕ) (S := ℕ) (Fin n) A).1,
        StableGL.of
          (Matrix.GeneralLinearGroup.prodSemiringEquiv (R := ℕ) (S := ℕ) (Fin n) A).2) :=
  StableGL.prodEquiv_of A

example (x : StableGL (ℕ × ℕ)) :
    StableGL.prodEquiv ℕ ℕ
        (StableGL.functor.map
          (SemiRingCat.ofHom ((RingHom.id ℕ).prodMap (RingHom.id ℕ))) x) =
      (StableGL.functor.map (SemiRingCat.ofHom (RingHom.id ℕ))
          (StableGL.prodEquiv ℕ ℕ x).1,
        StableGL.functor.map (SemiRingCat.ofHom (RingHom.id ℕ))
          (StableGL.prodEquiv ℕ ℕ x).2) :=
  StableGL.prodEquiv_mapRingHom (RingHom.id ℕ) (RingHom.id ℕ) x

end MathlibExtTest.KTheory.Ring.StableGeneralLinear.ProductTests

end
