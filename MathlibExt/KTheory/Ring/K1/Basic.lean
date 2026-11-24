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

public import MathlibExt.KTheory.Ring.StableGeneralLinear.Basic
public import MathlibExt.KTheory.Ring.StableGeneralLinear.ScalarMap
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.GroupTheory.Abelianization.Defs

/-! # Algebraic K₁ via stable general linear groups

This file also packages ordinary same-universe ring-isomorphism invariance via
`K1.functor`. This is not a claim of general Morita invariance.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace AlgebraicKTheory

noncomputable section

/-- `K₁` as the abelianization of the stable general linear group, functorially in rings. -/
noncomputable def K1.functor : RingCat.{u} ⥤ AddCommGrpCat.{u} :=
  forget₂ RingCat SemiRingCat ⋙ StableGL.functor ⋙ GrpCat.abelianize ⋙ CommGrpCat.toAddCommGrp

/-- The underlying type of `K₁(R)`. -/
abbrev K1 (R : Type u) [Ring R] : Type u :=
  ↥(K1.functor.obj (RingCat.of R))

/-- Canonical projection `StableGL R → K₁ R`. -/
def K1.proj {R : Type u} [Ring R] (g : StableGL R) : K1 R :=
  Additive.ofMul (Group.Abelianization.of g)

theorem K1.proj_def {R : Type u} [Ring R] (g : StableGL R) :
    K1.proj (R := R) g = Additive.ofMul (Group.Abelianization.of g) :=
  rfl

/-- Every classical `K₁` class has a stable general-linear representative. -/
theorem K1.proj_surjective (R : Type u) [Ring R] :
    Function.Surjective (K1.proj (R := R)) := by
  have h_of : Function.Surjective
      (Group.Abelianization.of (G := StableGL R)) :=
    QuotientGroup.mk'_surjective _
  have h_add : Function.Surjective
      (Additive.ofMul : Group.Abelianization (StableGL R) → K1 R) := by
    intro x
    exact ⟨Additive.toMul x, ofMul_toMul x⟩
  have h_eq : K1.proj (R := R) =
      Additive.ofMul ∘ Group.Abelianization.of (G := StableGL R) := rfl
  rw [h_eq]
  exact h_add.comp h_of

/-- Finite-stage generator `GLₙ(R) → K₁(R)`. -/
def K1.mk {R : Type u} [Ring R] {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) R) : K1 R :=
  K1.proj (StableGL.of g)

theorem K1.mk_def {R : Type u} [Ring R] {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    K1.mk g = Additive.ofMul (Group.Abelianization.of (StableGL.of g)) :=
  rfl

theorem K1.mk_eq_proj_of {R : Type u} [Ring R] {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    K1.mk g = K1.proj (StableGL.of g) :=
  rfl

/-- For rings `R, S : Type u`, a ring homomorphism `f : R →+* S`, and `g : StableGL R`,
`K1.functor.map (RingCat.ofHom f)` sends `K1.proj g` to the projection
of `(StableGL.functor.map (SemiRingCat.ofHom f)) g` in `K1 S`. -/
theorem K1.functor_map_proj {R S : Type u} [Ring R] [Ring S]
    (f : R →+* S) (g : StableGL R) :
    (K1.functor.map (RingCat.ofHom f)) (K1.proj g) =
      K1.proj ((StableGL.functor.map (SemiRingCat.ofHom f)) g) :=
  rfl

/-- For rings `R, S : Type u`, a ring homomorphism `f : R →+* S`, and
`g : Matrix.GeneralLinearGroup (Fin n) R`, `K1.functor.map (RingCat.ofHom f)`
sends `K1.mk g` to `K1.mk (Matrix.GeneralLinearGroup.mapRingHom f g)` in `K1 S`. -/
theorem K1.functor_map_mk {R S : Type u} [Ring R] [Ring S]
    (f : R →+* S) {n : ℕ} (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (K1.functor.map (RingCat.ofHom f)) (K1.mk g) =
      K1.mk (Matrix.GeneralLinearGroup.mapRingHom f g) := by
  calc
    (K1.functor.map (RingCat.ofHom f)) (K1.mk g)
        = (K1.functor.map (RingCat.ofHom f)) (K1.proj (StableGL.of g)) := rfl
    _ = K1.proj ((StableGL.functor.map (SemiRingCat.ofHom f)) (StableGL.of g)) := rfl
    _ = K1.proj (StableGL.of (Matrix.GeneralLinearGroup.mapRingHom f g)) := by
        rw [StableGL.map_of]
    _ = K1.mk (Matrix.GeneralLinearGroup.mapRingHom f g) := rfl

namespace K1

variable {R : Type u} {S : Type v} {T : Type w} [Ring R] [Ring S] [Ring T]

/-- For rings `R : Type u` and `S : Type v`, a ring homomorphism `f : R →+* S`
induces an additive homomorphism `K1 R →+ K1 S` via the abelianization of
`StableGL.scalarMap f`. Unlike `K1.functor`, this map allows independent universes. -/
noncomputable def mapRingHom (f : R →+* S) : K1 R →+ K1 S :=
  (Group.Abelianization.map (StableGL.scalarMap f)).toAdditive

/-- For a ring homomorphism `f : R →+* S` between rings in independent universes,
`mapRingHom f` equals `(Group.Abelianization.map (StableGL.scalarMap f)).toAdditive`
as a bundled additive homomorphism `K1 R →+ K1 S`. -/
theorem mapRingHom_value (f : R →+* S) :
    mapRingHom f = (Group.Abelianization.map (StableGL.scalarMap f)).toAdditive := rfl

/-- For a ring homomorphism `f : R →+* S` between rings in independent universes
and `g : StableGL R`, `mapRingHom f (K1.proj g) = K1.proj (StableGL.scalarMap f g)`. -/
@[simp]
theorem mapRingHom_proj (f : R →+* S) (g : StableGL R) :
    mapRingHom f (K1.proj g) =
      K1.proj (StableGL.scalarMap f g) := rfl

/-- For a ring homomorphism `f : R →+* S` between rings in independent universes and
`g : Matrix.GeneralLinearGroup (Fin n) R`, `mapRingHom f` sends `K1.mk g` to
`K1.mk (Matrix.GeneralLinearGroup.mapRingHom f g)`. -/
@[simp]
theorem mapRingHom_mk (f : R →+* S) {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    mapRingHom f (K1.mk g) =
      K1.mk (Matrix.GeneralLinearGroup.mapRingHom f g) := by
  exact (mapRingHom_proj f (StableGL.of g)).trans
    (congrArg K1.proj (StableGL.scalarMap_of f g))

/-- For any ring `R`, the map `mapRingHom (RingHom.id R)` is the identity
additive homomorphism `AddMonoidHom.id (K1 R)`. -/
@[simp]
theorem mapRingHom_id (R : Type u) [Ring R] :
    mapRingHom (RingHom.id R) = AddMonoidHom.id (K1 R) := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨g, rfl⟩ := K1.proj_surjective R x
  have h := congrArg (fun k : StableGL R →* StableGL R => k g) (StableGL.scalarMap_id R)
  exact (mapRingHom_proj (RingHom.id R) g).trans (congrArg K1.proj h)

/-- For ring homomorphisms `f : R →+* S` and `g : S →+* T` between rings
in independent universes, `mapRingHom (g.comp f) = (mapRingHom g).comp (mapRingHom f)`
as additive homomorphisms `K1 R →+ K1 T`. -/
theorem mapRingHom_comp (f : R →+* S) (g : S →+* T) :
    mapRingHom (g.comp f) = (mapRingHom g).comp (mapRingHom f) := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨a, rfl⟩ := K1.proj_surjective R x
  have h := congrArg (fun k : StableGL R →* StableGL T => k a)
    (StableGL.scalarMap_comp f g)
  have hFirst := mapRingHom_proj f a
  have hSecond := mapRingHom_proj g (StableGL.scalarMap f a)
  exact (mapRingHom_proj (g.comp f) a).trans
    ((congrArg K1.proj h).trans
      (hSecond.symm.trans (congrArg (mapRingHom g) hFirst.symm)))

/-- For rings `R, S : Type u` and a ring homomorphism `f : R →+* S`, the
coefficient map `mapRingHom f` equals the bundled additive homomorphism
`(K1.functor.map (RingCat.ofHom f)).hom : K1 R →+ K1 S`. -/
theorem mapRingHom_eq_functor {R S : Type u} [Ring R] [Ring S] (f : R →+* S) :
    mapRingHom f = (functor.map (RingCat.ofHom f)).hom := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨g, rfl⟩ := K1.proj_surjective R x
  have h := congrArg (fun k : StableGL R →* StableGL S => k g)
    (StableGL.scalarMap_eq_functor f)
  exact (mapRingHom_proj f g).trans
    ((congrArg K1.proj h).trans (functor_map_proj f g).symm)

end K1

/-! ### Ring-equivalence transport -/

/-- For rings `R, S : Type u`, a ring equivalence `e : R ≃+* S` induces the
additive equivalence `K1 R ≃+ K1 S` obtained by applying `K1.functor` to
the isomorphism of rings corresponding to `e`. -/
noncomputable def K1.equivOfRingEquiv {R S : Type u} [Ring R] [Ring S]
    (e : R ≃+* S) : K1 R ≃+ K1 S :=
  Iso.addCommGroupIsoToAddEquiv (K1.functor.mapIso e.toRingCatIso)

/-- For rings `R, S : Type u` and a ring equivalence `e : R ≃+* S`, the
bundled additive homomorphism `(K1.equivOfRingEquiv e).toAddMonoidHom : K1 R →+ K1 S`
equals `K1.mapRingHom e.toRingHom`. -/
theorem K1.equivOfRingEquiv_toAddMonoidHom
    {R S : Type u} [Ring R] [Ring S] (e : R ≃+* S) :
    (K1.equivOfRingEquiv e).toAddMonoidHom =
      K1.mapRingHom e.toRingHom :=
  (K1.mapRingHom_eq_functor e.toRingHom).symm

/-- For rings `R, S : Type u`, a ring equivalence `e : R ≃+* S`, and `x : K1 R`,
`K1.equivOfRingEquiv e x = K1.mapRingHom e.toRingHom x` in `K1 S`. -/
theorem K1.equivOfRingEquiv_apply
    {R S : Type u} [Ring R] [Ring S] (e : R ≃+* S) (x : K1 R) :
    K1.equivOfRingEquiv e x =
      K1.mapRingHom e.toRingHom x :=
  congrArg (fun h : K1 R →+ K1 S => h x) (K1.equivOfRingEquiv_toAddMonoidHom e)

/-- For any ring `R`, transport along `RingEquiv.refl R` equals the identity
additive equivalence `AddEquiv.refl (K1 R) : K1 R ≃+ K1 R`. -/
@[simp]
theorem K1.equivOfRingEquiv_id (R : Type u) [Ring R] :
    K1.equivOfRingEquiv (RingEquiv.refl R) = AddEquiv.refl (K1 R) := by
  apply AddEquiv.ext
  intro x
  rw [K1.equivOfRingEquiv_apply]
  change K1.mapRingHom (RingHom.id R) x = x
  rw [K1.mapRingHom_id]
  rfl

/-- For any ring `R` and `x : K1 R`, `K1.equivOfRingEquiv (RingEquiv.refl R) x = x`. -/
theorem K1.equivOfRingEquiv_id_apply (R : Type u) [Ring R] (x : K1 R) :
    K1.equivOfRingEquiv (RingEquiv.refl R) x = x := by
  rw [K1.equivOfRingEquiv_id]
  rfl

/-- For rings `R, S, T : Type u` and ring equivalences `e : R ≃+* S` and
`e′ : S ≃+* T`, transport along `e.trans e′` is the composite of transport
along `e` followed by transport along `e′`, as equivalences `K1 R ≃+ K1 T`. -/
@[simp]
theorem K1.equivOfRingEquiv_comp
    {R S T : Type u} [Ring R] [Ring S] [Ring T]
    (e : R ≃+* S) (e' : S ≃+* T) :
    K1.equivOfRingEquiv (e.trans e') =
      (K1.equivOfRingEquiv e).trans (K1.equivOfRingEquiv e') := by
  apply AddEquiv.ext
  intro x
  change K1.equivOfRingEquiv (e.trans e') x =
    K1.equivOfRingEquiv e' (K1.equivOfRingEquiv e x)
  rw [K1.equivOfRingEquiv_apply, K1.equivOfRingEquiv_apply, K1.equivOfRingEquiv_apply]
  change K1.mapRingHom (e'.toRingHom.comp e.toRingHom) x =
    K1.mapRingHom e'.toRingHom (K1.mapRingHom e.toRingHom x)
  rw [K1.mapRingHom_comp]
  rfl

/-- For rings `R, S, T : Type u`, ring equivalences `e : R ≃+* S` and
`e′ : S ≃+* T`, and `x : K1 R`, transport along `e.trans e′` sends `x` to
`K1.equivOfRingEquiv e′ (K1.equivOfRingEquiv e x)` in `K1 T`. -/
theorem K1.equivOfRingEquiv_comp_apply
    {R S T : Type u} [Ring R] [Ring S] [Ring T]
    (e : R ≃+* S) (e' : S ≃+* T) (x : K1 R) :
    K1.equivOfRingEquiv (e.trans e') x =
      K1.equivOfRingEquiv e' (K1.equivOfRingEquiv e x) := by
  rw [K1.equivOfRingEquiv_comp]
  rfl

/-- For rings `R, S : Type u` and a ring equivalence `e : R ≃+* S`,
`K1.equivOfRingEquiv e.symm = (K1.equivOfRingEquiv e).symm` as additive
equivalences `K1 S ≃+ K1 R`. -/
@[simp]
theorem K1.equivOfRingEquiv_symm
    {R S : Type u} [Ring R] [Ring S] (e : R ≃+* S) :
    K1.equivOfRingEquiv e.symm = (K1.equivOfRingEquiv e).symm := by
  apply AddEquiv.ext
  intro x
  apply (K1.equivOfRingEquiv e).injective
  calc
    K1.equivOfRingEquiv e (K1.equivOfRingEquiv e.symm x) =
        K1.equivOfRingEquiv (e.symm.trans e) x := by
      rw [K1.equivOfRingEquiv_comp_apply]
    _ = x := by simp
    _ = K1.equivOfRingEquiv e ((K1.equivOfRingEquiv e).symm x) := by
      rw [AddEquiv.apply_symm_apply]

/-- For rings `R, S : Type u`, a ring equivalence `e : R ≃+* S`, and `x : K1 S`,
`K1.equivOfRingEquiv e.symm x = (K1.equivOfRingEquiv e).symm x` in `K1 R`. -/
theorem K1.equivOfRingEquiv_symm_apply
    {R S : Type u} [Ring R] [Ring S] (e : R ≃+* S) (x : K1 S) :
    K1.equivOfRingEquiv e.symm x = (K1.equivOfRingEquiv e).symm x := by
  rw [K1.equivOfRingEquiv_symm]

/-- For rings `R, S : Type u`, a ring equivalence `e : R ≃+* S`, and `g : StableGL R`,
`K1.equivOfRingEquiv e` sends `K1.proj g` to `K1.proj` applied to the image of `g`
under `StableGL.functor.map (SemiRingCat.ofHom e.toRingHom)` in `StableGL S`. -/
@[simp]
theorem K1.equivOfRingEquiv_proj {R S : Type u} [Ring R] [Ring S]
    (e : R ≃+* S) (g : StableGL R) :
    K1.equivOfRingEquiv e (K1.proj g) =
      K1.proj ((StableGL.functor.map (SemiRingCat.ofHom (e : R →+* S))) g) := by
  rw [K1.equivOfRingEquiv_apply, K1.mapRingHom_eq_functor]
  exact K1.functor_map_proj (e : R →+* S) g

/-- For rings `R, S : Type u`, a ring equivalence `e : R ≃+* S`, and
`g : Matrix.GeneralLinearGroup (Fin n) R`, `K1.equivOfRingEquiv e (K1.mk g)`
equals `K1.mk (Matrix.GeneralLinearGroup.mapRingHom e.toRingHom g)` in `K1 S`. -/
@[simp]
theorem K1.equivOfRingEquiv_mk {R S : Type u} [Ring R] [Ring S]
    (e : R ≃+* S) {n : ℕ} (g : Matrix.GeneralLinearGroup (Fin n) R) :
    K1.equivOfRingEquiv e (K1.mk g) =
      K1.mk (Matrix.GeneralLinearGroup.mapRingHom (e : R →+* S) g) := by
  rw [K1.equivOfRingEquiv_apply]
  exact K1.mapRingHom_mk (e : R →+* S) g

end

end AlgebraicKTheory

end
