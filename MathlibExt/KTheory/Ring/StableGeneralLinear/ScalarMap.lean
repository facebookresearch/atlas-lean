/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.Basic
public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteScalarNaturality
public import Mathlib.CategoryTheory.Limits.Types.ColimitType

/-!
# Stable general linear coefficient maps in independent universes

A semiring homomorphism `f : R →+* S` induces a group homomorphism
`StableGL R →* StableGL S`, even when `R` and `S` lie in different universes.
On a finite representative it applies `f` entrywise and keeps the rank unchanged.
For semirings in the same universe, it agrees with the map of `StableGL.functor`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uR uS uT uA

namespace AlgebraicKTheory.StableGL

variable {R : Type uR} {S : Type uS} {T : Type uT}
variable [Semiring R] [Semiring S] [Semiring T]

private theorem stableOf_transition {A : Type uA} [Semiring A] {a b : ℕ}
    (p : a ⟶ b) (x : Matrix.GeneralLinearGroup (Fin a) A) :
    StableGL.of ((finiteGLDiagram.obj (SemiRingCat.of A)).map p x) = StableGL.of x := by
  apply StableGL.of_eq_iff.mpr
  refine ⟨b, 𝟙 b, p, ?_⟩
  rw [(finiteGLDiagram.obj (SemiRingCat.of A)).map_id]
  rfl

private theorem scalarImage_transition (f : R →+* S) {a b : ℕ} (p : a ⟶ b)
    (x : Matrix.GeneralLinearGroup (Fin a) R) :
    StableGL.of (Matrix.GeneralLinearGroup.mapRingHom f
        ((finiteGLDiagram.obj (SemiRingCat.of R)).map p x)) =
      StableGL.of (Matrix.GeneralLinearGroup.mapRingHom f x) := by
  exact (congrArg StableGL.of (finiteGLDiagram_mapRingHom_naturality f p x)).trans
    (stableOf_transition p (Matrix.GeneralLinearGroup.mapRingHom f x))

private def scalarCocone (f : R →+* S) :
    (finiteGLDiagram.obj (SemiRingCat.of R) ⋙ forget GrpCat.{uR}).CoconeTypes.{uS} where
  pt := StableGL S
  ι n x := StableGL.of (Matrix.GeneralLinearGroup.mapRingHom f
    (show Matrix.GeneralLinearGroup (Fin n) R from x))
  ι_naturality {a b} p := by
    funext x
    exact scalarImage_transition f p (show Matrix.GeneralLinearGroup (Fin a) R from x)

private def rawScalarMap (f : R →+* S) : StableGL R → StableGL S :=
  (finiteGLDiagram.obj (SemiRingCat.of R) ⋙ forget GrpCat.{uR}).descColimitType
    (scalarCocone f)

private theorem rawScalarMap_of (f : R →+* S) {n : ℕ}
    (x : Matrix.GeneralLinearGroup (Fin n) R) :
    rawScalarMap f (StableGL.of x) =
      StableGL.of (Matrix.GeneralLinearGroup.mapRingHom f x) := by
  rfl

private theorem stableOf_one (A : Type uA) [Semiring A] (n : ℕ) :
    StableGL.of (1 : Matrix.GeneralLinearGroup (Fin n) A) = (1 : StableGL A) :=
  ((StableGL.inclusion n).app (SemiRingCat.of A)).hom.map_one

private theorem stableOf_mul {A : Type uA} [Semiring A] {n : ℕ}
    (x y : Matrix.GeneralLinearGroup (Fin n) A) :
    StableGL.of (x * y) = StableGL.of x * StableGL.of y :=
  ((StableGL.inclusion n).app (SemiRingCat.of A)).hom.map_mul x y

private theorem rawScalarMap_one (f : R →+* S) :
    rawScalarMap f (1 : StableGL R) = (1 : StableGL S) := by
  calc
    _ = rawScalarMap f (StableGL.of (1 : Matrix.GeneralLinearGroup (Fin 0) R)) :=
      congrArg (rawScalarMap f) (stableOf_one R 0).symm
    _ = StableGL.of (Matrix.GeneralLinearGroup.mapRingHom f
          (1 : Matrix.GeneralLinearGroup (Fin 0) R)) := rawScalarMap_of f _
    _ = StableGL.of (1 : Matrix.GeneralLinearGroup (Fin 0) S) :=
      congrArg StableGL.of (Matrix.GeneralLinearGroup.mapRingHom (n := Fin 0) f).map_one
    _ = 1 := stableOf_one S 0

private theorem rawScalarMap_mul (f : R →+* S) (x y : StableGL R) :
    rawScalarMap f (x * y) = rawScalarMap f x * rawScalarMap f y := by
  obtain ⟨a, xa, rfl⟩ := StableGL.exists_finite_rep x
  obtain ⟨b, yb, rfl⟩ := StableGL.exists_finite_rep y
  let k := max a b
  let p : a ⟶ k := homOfLE (Nat.le_max_left _ _)
  let q : b ⟶ k := homOfLE (Nat.le_max_right _ _)
  let xk : Matrix.GeneralLinearGroup (Fin k) R :=
    (finiteGLDiagram.obj (SemiRingCat.of R)).map p xa
  let yk : Matrix.GeneralLinearGroup (Fin k) R :=
    (finiteGLDiagram.obj (SemiRingCat.of R)).map q yb
  have hmul : StableGL.of xa * StableGL.of yb = StableGL.of (xk * yk) :=
    GrpCat.FilteredColimits.colimit_mul_mk_eq
      (finiteGLDiagram.obj (SemiRingCat.of R)) ⟨a, xa⟩ ⟨b, yb⟩ k p q
  have hx : StableGL.of (Matrix.GeneralLinearGroup.mapRingHom f xk) =
      rawScalarMap f (StableGL.of xa) :=
    (scalarImage_transition f p xa).trans (rawScalarMap_of f xa).symm
  have hy : StableGL.of (Matrix.GeneralLinearGroup.mapRingHom f yk) =
      rawScalarMap f (StableGL.of yb) :=
    (scalarImage_transition f q yb).trans (rawScalarMap_of f yb).symm
  calc
    _ = rawScalarMap f (StableGL.of (xk * yk)) := congrArg (rawScalarMap f) hmul
    _ = StableGL.of (Matrix.GeneralLinearGroup.mapRingHom f (xk * yk)) := rawScalarMap_of f _
    _ = StableGL.of (Matrix.GeneralLinearGroup.mapRingHom f xk *
          Matrix.GeneralLinearGroup.mapRingHom f yk) :=
      congrArg StableGL.of ((Matrix.GeneralLinearGroup.mapRingHom f).map_mul xk yk)
    _ = StableGL.of (Matrix.GeneralLinearGroup.mapRingHom f xk) *
          StableGL.of (Matrix.GeneralLinearGroup.mapRingHom f yk) := stableOf_mul _ _
    _ = rawScalarMap f (StableGL.of xa) * rawScalarMap f (StableGL.of yb) :=
      congrArg₂ (fun z w : StableGL S => z * w) hx hy

/-- For a semiring homomorphism `f : R →+* S` between semirings in independent
universes, the stable coefficient homomorphism `StableGL R →* StableGL S` sends the
class of each rank-`n` invertible matrix to the class of its entrywise image under `f`. -/
public def scalarMap (f : R →+* S) : StableGL R →* StableGL S where
  toFun := rawScalarMap f
  map_one' := rawScalarMap_one f
  map_mul' := rawScalarMap_mul f

private theorem scalarMap_of_checked (f : R →+* S) {n : ℕ}
    (x : Matrix.GeneralLinearGroup (Fin n) R) :
    scalarMap f (StableGL.of x) =
      StableGL.of (Matrix.GeneralLinearGroup.mapRingHom f x) := rawScalarMap_of f x

/-- For semirings `R`, `S` in independent universes, `f : R →+* S`, and
`g : GL (Fin n) R`, `scalarMap f (StableGL.of g)` is
`StableGL.of (Matrix.GeneralLinearGroup.mapRingHom f g)` in `StableGL S`. -/
public theorem scalarMap_of (f : R →+* S) {n : ℕ}
    (x : Matrix.GeneralLinearGroup (Fin n) R) :
    scalarMap f (StableGL.of x) =
      StableGL.of (Matrix.GeneralLinearGroup.mapRingHom f x) := scalarMap_of_checked f x

/-- For semirings `R`, `S` in the same universe and `f : R →+* S`,
`scalarMap f` is the group homomorphism underlying
`StableGL.functor.map (SemiRingCat.ofHom f)`. The definition of `scalarMap` itself does
not require the universes to match. -/
public theorem scalarMap_eq_functor {A B : Type uA} [Semiring A] [Semiring B]
    (f : A →+* B) : scalarMap f = (StableGL.functor.map (SemiRingCat.ofHom f)).hom := by
  apply MonoidHom.ext
  intro x
  obtain ⟨n, xn, rfl⟩ := StableGL.exists_finite_rep x
  exact (scalarMap_of f xn).trans (StableGL.map_of f xn).symm

/-- For every semiring `R`, the bundled homomorphism
`scalarMap (RingHom.id R) : StableGL R →* StableGL R` equals `MonoidHom.id (StableGL R)`. -/
public theorem scalarMap_id (A : Type uA) [Semiring A] :
    scalarMap (RingHom.id A) = MonoidHom.id (StableGL A) := by
  apply MonoidHom.ext
  intro x
  obtain ⟨n, xn, rfl⟩ := StableGL.exists_finite_rep x
  have h : Matrix.GeneralLinearGroup.mapRingHom (RingHom.id A) xn = xn := by
    apply Units.ext
    apply Matrix.ext
    intro i j
    simp only [Matrix.GeneralLinearGroup.coe_mapRingHom, Matrix.map_apply, RingHom.id_apply]
  exact (scalarMap_of (RingHom.id A) xn).trans (congrArg StableGL.of h)

/-- For semirings `R`, `S`, `T` in independent universes and homomorphisms
`f : R →+* S`, `g : S →+* T`, the bundled maps satisfy
`scalarMap (g.comp f) = (scalarMap g).comp (scalarMap f)` from `StableGL R` to `StableGL T`. -/
public theorem scalarMap_comp (f : R →+* S) (g : S →+* T) :
    scalarMap (g.comp f) = (scalarMap g).comp (scalarMap f) := by
  apply MonoidHom.ext
  intro x
  obtain ⟨n, xn, rfl⟩ := StableGL.exists_finite_rep x
  have h : Matrix.GeneralLinearGroup.mapRingHom (g.comp f) xn =
      Matrix.GeneralLinearGroup.mapRingHom g (Matrix.GeneralLinearGroup.mapRingHom f xn) := by
    apply Units.ext
    apply Matrix.ext
    intro i j
    simp only [Matrix.GeneralLinearGroup.coe_mapRingHom, Matrix.map_apply, RingHom.comp_apply]
  have hR := scalarMap_of g (Matrix.GeneralLinearGroup.mapRingHom f xn)
  have hP := congrArg (scalarMap g) (scalarMap_of f xn)
  exact (scalarMap_of (g.comp f) xn).trans
    ((congrArg StableGL.of h).trans (hR.symm.trans hP.symm))

end AlgebraicKTheory.StableGL
