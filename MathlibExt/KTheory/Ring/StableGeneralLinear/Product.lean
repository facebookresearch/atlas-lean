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

public import MathlibExt.KTheory.Ring.StableGeneralLinear.Stabilization
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Product

/-!
# Stable general linear groups of product semirings

This file reuses the neutral entrywise equivalence
`GLₙ(R × S) ≃ GLₙ(R) × GLₙ(S)`, shows compatibility with the finite
stabilization diagram, and descends the forward
projection map to a multiplicative equivalence
`StableGL (R × S) ≃* StableGL R × StableGL S`.

The stable inverse is obtained from bijectivity of the projection map using
finite representatives.  No nonunital coordinate ring inclusion is used.
The two coefficient rings in the finite equivalences may live in independent
universes; the stable equivalence retains the stable functor's same-universe
scope.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory

universe u

namespace AlgebraicKTheory
namespace StableGL

variable {R S R' S' : Type u}
variable [Semiring R] [Semiring S] [Semiring R'] [Semiring S']

/-- The finite product equivalence commutes with every morphism in the
stabilization diagram. -/
theorem finite_prodEquiv_map {n m : ℕ} (f : n ⟶ m)
    (A : Matrix.GeneralLinearGroup (Fin n) (R × S)) :
    Matrix.GeneralLinearGroup.prodSemiringEquiv (R := R) (S := S) (Fin m)
        ((finiteGLDiagram.obj (SemiRingCat.of (R × S))).map f A) =
      ((finiteGLDiagram.obj (SemiRingCat.of R)).map f
          (Matrix.GeneralLinearGroup.prodSemiringEquiv (R := R) (S := S) (Fin n) A).1,
        (finiteGLDiagram.obj (SemiRingCat.of S)).map f
          (Matrix.GeneralLinearGroup.prodSemiringEquiv (R := R) (S := S) (Fin n) A).2) := by
  apply Prod.ext
  · have hnat := ConcreteCategory.congr_hom
      ((finiteGLDiagram.map (SemiRingCat.ofHom (RingHom.fst R S))).naturality f) A
    change Matrix.GeneralLinearGroup.mapRingHom (RingHom.fst R S)
        ((finiteGLDiagram.obj (SemiRingCat.of (R × S))).map f A) =
      (finiteGLDiagram.obj (SemiRingCat.of R)).map f
        (Matrix.GeneralLinearGroup.mapRingHom (RingHom.fst R S) A) at hnat
    exact hnat
  · have hnat := ConcreteCategory.congr_hom
      ((finiteGLDiagram.map (SemiRingCat.ofHom (RingHom.snd R S))).naturality f) A
    change Matrix.GeneralLinearGroup.mapRingHom (RingHom.snd R S)
        ((finiteGLDiagram.obj (SemiRingCat.of (R × S))).map f A) =
      (finiteGLDiagram.obj (SemiRingCat.of S)).map f
        (Matrix.GeneralLinearGroup.mapRingHom (RingHom.snd R S) A) at hnat
    exact hnat

/-- Forward stable product map, induced by the two unital ring projections. -/
noncomputable def prodHom (R S : Type u) [Semiring R] [Semiring S] :
    StableGL (R × S) →* StableGL R × StableGL S :=
  ((StableGL.functor.map
    (SemiRingCat.ofHom (RingHom.fst R S))).hom).prod
    ((StableGL.functor.map
      (SemiRingCat.ofHom (RingHom.snd R S))).hom)

/-- Forward formula for the stable product hom on a finite representative. -/
@[simp]
theorem prodHom_of {n : ℕ}
    (A : Matrix.GeneralLinearGroup (Fin n) (R × S)) :
    prodHom R S (StableGL.of A) =
      (StableGL.of
          (Matrix.GeneralLinearGroup.prodSemiringEquiv (R := R) (S := S) (Fin n) A).1,
        StableGL.of
          (Matrix.GeneralLinearGroup.prodSemiringEquiv (R := R) (S := S) (Fin n) A).2) := by
  apply Prod.ext
  · change StableGL.functor.map
      (SemiRingCat.ofHom (RingHom.fst R S)) (StableGL.of A) = _
    rw [StableGL.map_of, Matrix.GeneralLinearGroup.prodSemiringEquiv_apply_fst]
  · change StableGL.functor.map
      (SemiRingCat.ofHom (RingHom.snd R S)) (StableGL.of A) = _
    rw [StableGL.map_of, Matrix.GeneralLinearGroup.prodSemiringEquiv_apply_snd]

/-- The stable product projection map is surjective. Representatives in the
two coordinates are first moved to a common finite stage and then paired
entrywise. -/
theorem prodHom_surjective : Function.Surjective (prodHom R S) := by
  rintro ⟨x, y⟩
  obtain ⟨n₁, g₁, hg₁⟩ := StableGL.exists_finite_rep x
  obtain ⟨n₂, g₂, hg₂⟩ := StableGL.exists_finite_rep y
  let n := Nat.max n₁ n₂
  let f₁ : n₁ ⟶ n := homOfLE (Nat.le_max_left n₁ n₂)
  let f₂ : n₂ ⟶ n := homOfLE (Nat.le_max_right n₁ n₂)
  let g : Matrix.GeneralLinearGroup (Fin n) R :=
    (finiteGLDiagram.obj (SemiRingCat.of R)).map f₁ g₁
  let h : Matrix.GeneralLinearGroup (Fin n) S :=
    (finiteGLDiagram.obj (SemiRingCat.of S)).map f₂ g₂
  let A : Matrix.GeneralLinearGroup (Fin n) (R × S) :=
    (Matrix.GeneralLinearGroup.prodSemiringEquiv (R := R) (S := S) (Fin n)).symm (g, h)
  refine ⟨StableGL.of A, ?_⟩
  rw [prodHom_of]
  have hp := (Matrix.GeneralLinearGroup.prodSemiringEquiv
    (R := R) (S := S) (Fin n)).apply_symm_apply (g, h)
  apply Prod.ext
  · rw [show (Matrix.GeneralLinearGroup.prodSemiringEquiv
        (R := R) (S := S) (Fin n) A).1 = g from congrArg Prod.fst hp]
    exact (StableGL.of_map f₁ g₁).trans hg₁
  · rw [show (Matrix.GeneralLinearGroup.prodSemiringEquiv
        (R := R) (S := S) (Fin n) A).2 = h from congrArg Prod.snd hp]
    exact (StableGL.of_map f₂ g₂).trans hg₂

/-- The stable product projection map is injective. Coordinate equalities
are witnessed at finite stages; filteredness moves both witnesses to one
stage, where the finite product equivalence is injective. -/
theorem prodHom_injective : Function.Injective (prodHom R S) := by
  intro x y hxy
  obtain ⟨n, A, B, hA, hB⟩ := StableGL.exists_common_finite_rep x y
  have hxy' : prodHom R S (StableGL.of A) =
      prodHom R S (StableGL.of B) := by
    rw [hA, hB]
    exact hxy
  have hR : StableGL.of
      (Matrix.GeneralLinearGroup.prodSemiringEquiv (R := R) (S := S) (Fin n) A).1 =
      StableGL.of
        (Matrix.GeneralLinearGroup.prodSemiringEquiv (R := R) (S := S) (Fin n) B).1 := by
    simpa only [prodHom_of] using congrArg Prod.fst hxy'
  have hS : StableGL.of
      (Matrix.GeneralLinearGroup.prodSemiringEquiv (R := R) (S := S) (Fin n) A).2 =
      StableGL.of
        (Matrix.GeneralLinearGroup.prodSemiringEquiv (R := R) (S := S) (Fin n) B).2 := by
    simpa only [prodHom_of] using congrArg Prod.snd hxy'
  obtain ⟨kR, fR₁, fR₂, hRstage⟩ := StableGL.of_eq_iff.mp hR
  obtain ⟨kS, fS₁, fS₂, hSstage⟩ := StableGL.of_eq_iff.mp hS
  let k := Nat.max kR kS
  let uR : kR ⟶ k := homOfLE (Nat.le_max_left kR kS)
  let uS : kS ⟶ k := homOfLE (Nat.le_max_right kR kS)
  let a₁ : n ⟶ k := fR₁ ≫ uR
  let a₂ : n ⟶ k := fR₂ ≫ uR
  let b₁ : n ⟶ k := fS₁ ≫ uS
  let b₂ : n ⟶ k := fS₂ ≫ uS
  have hRfinal :
      (finiteGLDiagram.obj (SemiRingCat.of R)).map a₁
          (Matrix.GeneralLinearGroup.prodSemiringEquiv (R := R) (S := S) (Fin n) A).1 =
        (finiteGLDiagram.obj (SemiRingCat.of R)).map a₂
          (Matrix.GeneralLinearGroup.prodSemiringEquiv (R := R) (S := S) (Fin n) B).1 := by
    calc
      (finiteGLDiagram.obj (SemiRingCat.of R)).map a₁
          (Matrix.GeneralLinearGroup.prodSemiringEquiv (R := R) (S := S) (Fin n) A).1 =
          (finiteGLDiagram.obj (SemiRingCat.of R)).map uR
            ((finiteGLDiagram.obj (SemiRingCat.of R)).map fR₁
              (Matrix.GeneralLinearGroup.prodSemiringEquiv (R := R) (S := S) (Fin n) A).1) := by
            exact ConcreteCategory.congr_hom
              ((finiteGLDiagram.obj (SemiRingCat.of R)).map_comp fR₁ uR) _
      _ = (finiteGLDiagram.obj (SemiRingCat.of R)).map uR
            ((finiteGLDiagram.obj (SemiRingCat.of R)).map fR₂
              (Matrix.GeneralLinearGroup.prodSemiringEquiv (R := R) (S := S) (Fin n) B).1) := by
            rw [hRstage]
      _ = (finiteGLDiagram.obj (SemiRingCat.of R)).map a₂
          (Matrix.GeneralLinearGroup.prodSemiringEquiv (R := R) (S := S) (Fin n) B).1 := by
            exact (ConcreteCategory.congr_hom
              ((finiteGLDiagram.obj (SemiRingCat.of R)).map_comp fR₂ uR) _).symm
  have hSfinal :
      (finiteGLDiagram.obj (SemiRingCat.of S)).map b₁
          (Matrix.GeneralLinearGroup.prodSemiringEquiv (R := R) (S := S) (Fin n) A).2 =
        (finiteGLDiagram.obj (SemiRingCat.of S)).map b₂
          (Matrix.GeneralLinearGroup.prodSemiringEquiv (R := R) (S := S) (Fin n) B).2 := by
    calc
      (finiteGLDiagram.obj (SemiRingCat.of S)).map b₁
          (Matrix.GeneralLinearGroup.prodSemiringEquiv (R := R) (S := S) (Fin n) A).2 =
          (finiteGLDiagram.obj (SemiRingCat.of S)).map uS
            ((finiteGLDiagram.obj (SemiRingCat.of S)).map fS₁
              (Matrix.GeneralLinearGroup.prodSemiringEquiv (R := R) (S := S) (Fin n) A).2) := by
            exact ConcreteCategory.congr_hom
              ((finiteGLDiagram.obj (SemiRingCat.of S)).map_comp fS₁ uS) _
      _ = (finiteGLDiagram.obj (SemiRingCat.of S)).map uS
            ((finiteGLDiagram.obj (SemiRingCat.of S)).map fS₂
              (Matrix.GeneralLinearGroup.prodSemiringEquiv (R := R) (S := S) (Fin n) B).2) := by
            rw [hSstage]
      _ = (finiteGLDiagram.obj (SemiRingCat.of S)).map b₂
          (Matrix.GeneralLinearGroup.prodSemiringEquiv (R := R) (S := S) (Fin n) B).2 := by
            exact (ConcreteCategory.congr_hom
              ((finiteGLDiagram.obj (SemiRingCat.of S)).map_comp fS₂ uS) _).symm
  have hab₁ : a₁ = b₁ := Subsingleton.elim _ _
  have hab₂ : a₂ = b₂ := Subsingleton.elim _ _
  have hfinite :
      (finiteGLDiagram.obj (SemiRingCat.of (R × S))).map a₁ A =
        (finiteGLDiagram.obj (SemiRingCat.of (R × S))).map a₂ B := by
    apply (Matrix.GeneralLinearGroup.prodSemiringEquiv
      (R := R) (S := S) (Fin k)).injective
    rw [finite_prodEquiv_map, finite_prodEquiv_map]
    apply Prod.ext
    · exact hRfinal
    · rw [hab₁, hab₂]
      exact hSfinal
  have hOf : StableGL.of A = StableGL.of B :=
    StableGL.of_eq_iff.mpr ⟨k, a₁, a₂, hfinite⟩
  exact hA.symm.trans (hOf.trans hB)

/-- Stable general linear groups commute with binary products of rings. -/
noncomputable def prodEquiv (R S : Type u) [Semiring R] [Semiring S] :
    StableGL (R × S) ≃* StableGL R × StableGL S :=
  MulEquiv.ofBijective (prodHom R S)
    ⟨prodHom_injective (R := R) (S := S),
      prodHom_surjective (R := R) (S := S)⟩

/-- Forward formula for the stable equivalence on a finite representative. -/
theorem prodEquiv_of {n : ℕ}
    (A : Matrix.GeneralLinearGroup (Fin n) (R × S)) :
    prodEquiv R S (StableGL.of A) =
      (StableGL.of
          (Matrix.GeneralLinearGroup.prodSemiringEquiv (R := R) (S := S) (Fin n) A).1,
        StableGL.of
          (Matrix.GeneralLinearGroup.prodSemiringEquiv (R := R) (S := S) (Fin n) A).2) :=
  prodHom_of A

/-- Inverse formula for two finite representatives at a common rank. -/
theorem prodEquiv_symm_of_pair {n : ℕ}
    (A : Matrix.GeneralLinearGroup (Fin n) R)
    (B : Matrix.GeneralLinearGroup (Fin n) S) :
    (prodEquiv R S).symm (StableGL.of A, StableGL.of B) =
      StableGL.of
        ((Matrix.GeneralLinearGroup.prodSemiringEquiv
          (R := R) (S := S) (Fin n)).symm (A, B)) := by
  apply (prodEquiv R S).injective
  rw [MulEquiv.apply_symm_apply, prodEquiv_of,
    MulEquiv.apply_symm_apply]

/-- Naturality of the stable product equivalence for a pair of ring maps. -/
theorem prodEquiv_mapRingHom (f : R →+* R') (g : S →+* S')
    (x : StableGL (R × S)) :
    prodEquiv R' S'
        (StableGL.functor.map (SemiRingCat.ofHom (f.prodMap g)) x) =
      (StableGL.functor.map (SemiRingCat.ofHom f) (prodEquiv R S x).1,
        StableGL.functor.map (SemiRingCat.ofHom g) (prodEquiv R S x).2) := by
  obtain ⟨n, A, rfl⟩ := StableGL.exists_finite_rep x
  rw [StableGL.map_of, prodEquiv_of, prodEquiv_of,
    Matrix.GeneralLinearGroup.prodSemiringEquiv_mapRingHom,
    StableGL.map_of, StableGL.map_of]

end StableGL
end AlgebraicKTheory

end
