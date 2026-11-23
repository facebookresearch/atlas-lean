/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
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
  Additive.ofMul (Abelianization.of g)

theorem K1.proj_def {R : Type u} [Ring R] (g : StableGL R) :
    K1.proj (R := R) g = Additive.ofMul (Abelianization.of g) :=
  rfl

/-- Every classical `K₁` class has a stable general-linear representative. -/
theorem K1.proj_surjective (R : Type u) [Ring R] :
    Function.Surjective (K1.proj (R := R)) := by
  have h_of : Function.Surjective
      (Abelianization.of (G := StableGL R)) :=
    QuotientGroup.mk'_surjective _
  have h_add : Function.Surjective
      (Additive.ofMul : Abelianization (StableGL R) → K1 R) := by
    intro x
    exact ⟨Additive.toMul x, ofMul_toMul x⟩
  have h_eq : K1.proj (R := R) =
      Additive.ofMul ∘ Abelianization.of (G := StableGL R) := rfl
  rw [h_eq]
  exact h_add.comp h_of

/-- Finite-stage generator `GLₙ(R) → K₁(R)`. -/
def K1.mk {R : Type u} [Ring R] {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) R) : K1 R :=
  K1.proj (StableGL.of g)

theorem K1.mk_def {R : Type u} [Ring R] {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    K1.mk g = Additive.ofMul (Abelianization.of (StableGL.of g)) :=
  rfl

theorem K1.mk_eq_proj_of {R : Type u} [Ring R] {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    K1.mk g = K1.proj (StableGL.of g) :=
  rfl

/-- Functoriality on stable representatives. -/
theorem K1.functor_map_proj {R S : Type u} [Ring R] [Ring S]
    (f : R →+* S) (g : StableGL R) :
    (K1.functor.map (RingCat.ofHom f)) (K1.proj g) =
      K1.proj ((StableGL.functor.map (SemiRingCat.ofHom f)) g) :=
  rfl

/-- Functoriality on finite `K₁` generators. -/
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

/-- The canonical coefficient map on `K₁` for rings in independent universes. -/
noncomputable def mapRingHom (f : R →+* S) : K1 R →+ K1 S :=
  (Abelianization.map (StableGL.scalarMap f)).toAdditive

/-- The coefficient map is induced by the original stable scalar map on abelianizations. -/
theorem mapRingHom_value (f : R →+* S) :
    mapRingHom f = (Abelianization.map (StableGL.scalarMap f)).toAdditive := rfl

/-- A ring homomorphism acts on stable `K₁` representatives by the stable scalar map. -/
@[simp]
theorem mapRingHom_proj (f : R →+* S) (g : StableGL R) :
    mapRingHom f (K1.proj g) =
      K1.proj (StableGL.scalarMap f g) := rfl

/-- A ring homomorphism acts on finite-stage `K₁` generators by applying the
homomorphism entrywise. -/
@[simp]
theorem mapRingHom_mk (f : R →+* S) {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    mapRingHom f (K1.mk g) =
      K1.mk (Matrix.GeneralLinearGroup.mapRingHom f g) := by
  exact (mapRingHom_proj f (StableGL.of g)).trans
    (congrArg K1.proj (StableGL.scalarMap_of f g))

/-- The identity ring homomorphism induces the identity on `K₁`. -/
@[simp]
theorem mapRingHom_id (R : Type u) [Ring R] :
    mapRingHom (RingHom.id R) = AddMonoidHom.id (K1 R) := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨g, rfl⟩ := K1.proj_surjective R x
  have h := congrArg (fun k : StableGL R →* StableGL R => k g) (StableGL.scalarMap_id R)
  exact (mapRingHom_proj (RingHom.id R) g).trans (congrArg K1.proj h)

/-- Maps on `K₁` respect composition of ring homomorphisms. -/
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

/-- At one ring universe the canonical map is the original `K1.functor` map. -/
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

/-- Ordinary ring-isomorphism invariance for classical `K₁`: transport along
a ring equivalence via `K1.functor`. This is ordinary ring-isomorphism
invariance, not general Morita invariance. -/
noncomputable def K1.equivOfRingEquiv {R S : Type u} [Ring R] [Ring S]
    (e : R ≃+* S) : K1 R ≃+ K1 S :=
  Iso.addCommGroupIsoToAddEquiv (K1.functor.mapIso e.toRingCatIso)

/-- The additive homomorphism underlying `K1.equivOfRingEquiv` is the map of
`K1.functor` on the forward ring homomorphism. -/
theorem K1.equivOfRingEquiv_toAddMonoidHom
    {R S : Type u} [Ring R] [Ring S] (e : R ≃+* S) :
    (K1.equivOfRingEquiv e).toAddMonoidHom =
      K1.mapRingHom e.toRingHom :=
  (K1.mapRingHom_eq_functor e.toRingHom).symm

/-- Pointwise form of `K1.equivOfRingEquiv_toAddMonoidHom`.

This generic bridge is intentionally not a simp lemma: the specialized
`proj` and `mk` rules below preserve the useful generator normal forms. -/
theorem K1.equivOfRingEquiv_apply
    {R S : Type u} [Ring R] [Ring S] (e : R ≃+* S) (x : K1 R) :
    K1.equivOfRingEquiv e x =
      K1.mapRingHom e.toRingHom x :=
  congrArg (fun h : K1 R →+ K1 S => h x) (K1.equivOfRingEquiv_toAddMonoidHom e)

/-- Transport along the identity ring equivalence is the identity. -/
@[simp]
theorem K1.equivOfRingEquiv_id (R : Type u) [Ring R] :
    K1.equivOfRingEquiv (RingEquiv.refl R) = AddEquiv.refl (K1 R) := by
  apply AddEquiv.ext
  intro x
  rw [K1.equivOfRingEquiv_apply]
  change K1.mapRingHom (RingHom.id R) x = x
  rw [K1.mapRingHom_id]
  rfl

/-- Pointwise identity law for ring-equivalence transport. -/
theorem K1.equivOfRingEquiv_id_apply (R : Type u) [Ring R] (x : K1 R) :
    K1.equivOfRingEquiv (RingEquiv.refl R) x = x := by
  rw [K1.equivOfRingEquiv_id]
  rfl

/-- Transport respects composition of ring equivalences, in forward order. -/
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

/-- Pointwise composition law for ring-equivalence transport. -/
theorem K1.equivOfRingEquiv_comp_apply
    {R S T : Type u} [Ring R] [Ring S] [Ring T]
    (e : R ≃+* S) (e' : S ≃+* T) (x : K1 R) :
    K1.equivOfRingEquiv (e.trans e') x =
      K1.equivOfRingEquiv e' (K1.equivOfRingEquiv e x) := by
  rw [K1.equivOfRingEquiv_comp]
  rfl

/-- Transport along the inverse ring equivalence is the inverse additive
equivalence. -/
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

/-- Pointwise inverse law for ring-equivalence transport. -/
theorem K1.equivOfRingEquiv_symm_apply
    {R S : Type u} [Ring R] [Ring S] (e : R ≃+* S) (x : K1 S) :
    K1.equivOfRingEquiv e.symm x = (K1.equivOfRingEquiv e).symm x := by
  rw [K1.equivOfRingEquiv_symm]

/-- Projection formula for `K1.equivOfRingEquiv`: `K1.proj` maps via the
stable-level functor map, oriented from `R` to `S`. -/
@[simp]
theorem K1.equivOfRingEquiv_proj {R S : Type u} [Ring R] [Ring S]
    (e : R ≃+* S) (g : StableGL R) :
    K1.equivOfRingEquiv e (K1.proj g) =
      K1.proj ((StableGL.functor.map (SemiRingCat.ofHom (e : R →+* S))) g) := by
  rw [K1.equivOfRingEquiv_apply, K1.mapRingHom_eq_functor]
  exact K1.functor_map_proj (e : R →+* S) g

/-- Finite generator formula for `K1.equivOfRingEquiv`: `K1.mk` maps via
`Matrix.GeneralLinearGroup.mapRingHom`, oriented from `R` to `S`. -/
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
