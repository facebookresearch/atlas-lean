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

public import MathlibExt.KTheory.Ring.K2.Functoriality
public import MathlibExt.KTheory.Ring.K2.StableSteinbergCentrality
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup

/-! # Abelian and functorial algebraic `K₂`

Stable centrality gives the additive functor `K2.addCommGrpFunctor`.  This file
also packages its ordinary same-universe ring-isomorphism invariance.  This is
algebraic `K₂` (the stable Steinberg kernel), not Milnor `K₂`, and no general
Morita invariance is claimed.
-/

@[expose] public section

open CategoryTheory

open scoped IsMulCommutative

universe u

namespace AlgebraicKTheory

namespace K2

/-- `K₂ R` is commutative via centrality of `ker StableSteinberg.toStableE`. -/
instance instIsMulCommutative (R : Type u) [Ring R] : IsMulCommutative (K2 R) :=
  IsMulCommutative.of_comm fun a b => by
    have hInj : Function.Injective (K2.inclusion.app (RingCat.of R)) := by
      have hMono : Mono (K2.inclusion.app (RingCat.of R)) := by
        rw [K2.inclusion_app]
        exact CategoryTheory.Limits.equalizer.ι_mono
      exact (GrpCat.mono_iff_injective _).mp hMono
    apply hInj
    have h_center : K2.inclusion.app (RingCat.of R) a ∈ Subgroup.center (StableSteinberg R) :=
      StableSteinberg.ker_toStableE_le_center (K2.inclusion_apply_mem_ker a)
    have h_comm : K2.inclusion.app (RingCat.of R) a * K2.inclusion.app (RingCat.of R) b =
        K2.inclusion.app (RingCat.of R) b * K2.inclusion.app (RingCat.of R) a :=
      (Subgroup.mem_center_iff.mp h_center (K2.inclusion.app (RingCat.of R) b)).symm
    calc K2.inclusion.app (RingCat.of R) (a * b)
        = K2.inclusion.app (RingCat.of R) a * K2.inclusion.app (RingCat.of R) b :=
          map_mul (K2.inclusion.app (RingCat.of R)).hom a b
      _ = K2.inclusion.app (RingCat.of R) b * K2.inclusion.app (RingCat.of R) a := h_comm
      _ = K2.inclusion.app (RingCat.of R) (b * a) :=
          (map_mul (K2.inclusion.app (RingCat.of R)).hom b a).symm

/-- Additive `K₂` functor `RingCat ⥤ AddCommGrpCat` via `Additive` transport. -/
noncomputable def addCommGrpFunctor : RingCat.{u} ⥤ AddCommGrpCat.{u} where
  obj R := AddCommGrpCat.of (Additive (K2 (R : Type u)))
  map {R S} f := AddCommGrpCat.ofHom (K2.mapRingHom f.hom).toAdditive
  map_id R := by
    have hhom : (𝟙 R : R ⟶ R).hom = RingHom.id (R : Type u) := rfl
    rw [hhom, K2.mapRingHom_id]
    rfl
  map_comp {R S T} f g := by
    have hhom : (f ≫ g).hom = g.hom.comp f.hom := rfl
    rw [hhom, K2.mapRingHom_comp]
    rfl

@[simp]
theorem addCommGrpFunctor_obj (R : RingCat.{u}) :
    addCommGrpFunctor.obj R = AddCommGrpCat.of (Additive (K2 (R : Type u))) :=
  rfl

@[simp]
theorem addCommGrpFunctor_map_ofHom {R S : Type u} [Ring R] [Ring S] (f : R →+* S) :
    addCommGrpFunctor.map (RingCat.ofHom f) = AddCommGrpCat.ofHom (K2.mapRingHom f).toAdditive :=
  rfl

/-! ### Ring-equivalence transport -/

variable {R S : Type u} [Ring R] [Ring S]

/-- Additive equivalence `Additive (K₂ R) ≃+ Additive (K₂ S)` induced by a
same-universe ring equivalence `e : R ≃+* S`, via `K2.addCommGrpFunctor`.

Orientation: forward along `e`. Inverse is `equivOfRingEquiv e.symm`.
Same-universe scope is intentional. -/
noncomputable def equivOfRingEquiv (e : R ≃+* S) :
    Additive (K2 R) ≃+ Additive (K2 S) :=
  (K2.addCommGrpFunctor.mapIso e.toRingCatIso).addCommGroupIsoToAddEquiv

/-- The additive homomorphism underlying `equivOfRingEquiv` is the map of
`K2.addCommGrpFunctor` on the forward ring homomorphism. -/
theorem equivOfRingEquiv_toAddMonoidHom (e : R ≃+* S) :
    (equivOfRingEquiv e).toAddMonoidHom =
      (K2.addCommGrpFunctor.map (RingCat.ofHom e.toRingHom)).hom :=
  rfl

/-- Pointwise form of `equivOfRingEquiv_toAddMonoidHom`.

This generic bridge is intentionally not a simp lemma: the specialized
`ofMul` rule below preserves the multiplicative `K₂` normal form. -/
theorem equivOfRingEquiv_apply (e : R ≃+* S) (x : Additive (K2 R)) :
    equivOfRingEquiv e x =
      K2.addCommGrpFunctor.map (RingCat.ofHom e.toRingHom) x :=
  rfl

/-- Focused transport formula: `equivOfRingEquiv` sends `Additive.ofMul x` to
`Additive.ofMul (K2.mapRingHom e.toRingHom x)`, reusing the existing
functorial map. Oriented from `R` to `S`. -/
@[simp]
theorem equivOfRingEquiv_ofMul (e : R ≃+* S) (x : K2 R) :
    equivOfRingEquiv e (Additive.ofMul x) =
      Additive.ofMul (K2.mapRingHom e.toRingHom x) :=
  rfl

/-- Identity law for `K2.equivOfRingEquiv`: transport along `RingEquiv.refl`
is the identity. Same-universe only; no Morita, Milnor, symbol/Matsumoto,
or product claim. -/
@[simp]
theorem equivOfRingEquiv_id (R : Type u) [Ring R] :
    K2.equivOfRingEquiv (RingEquiv.refl R) = AddEquiv.refl (Additive (K2 R)) := by
  ext x
  change Additive.ofMul (K2.mapRingHom (RingHom.id R) x.toMul) = x
  rw [K2.mapRingHom_id]
  exact ofMul_toMul x

/-- Pointwise identity law for `K2.equivOfRingEquiv`. -/
@[simp]
theorem equivOfRingEquiv_id_apply (R : Type u) [Ring R]
    (x : Additive (K2 R)) :
    K2.equivOfRingEquiv (RingEquiv.refl R) x = x := by
  rw [equivOfRingEquiv_id]
  rfl

/-- Composition law for `K2.equivOfRingEquiv`, oriented along `RingEquiv.trans`:
transport along `e.trans e'` equals the composite of the transports.
Same-universe only; no Morita, Milnor, symbol/Matsumoto or product claim. -/
@[simp]
theorem equivOfRingEquiv_comp {R S T : Type u} [Ring R] [Ring S] [Ring T]
    (e : R ≃+* S) (e' : S ≃+* T) :
    K2.equivOfRingEquiv (e.trans e') =
      (K2.equivOfRingEquiv e).trans (K2.equivOfRingEquiv e') := by
  ext x
  change Additive.ofMul
      (K2.mapRingHom (e'.toRingHom.comp e.toRingHom) x.toMul) =
    Additive.ofMul
      (K2.mapRingHom e'.toRingHom (K2.mapRingHom e.toRingHom x.toMul))
  rw [K2.mapRingHom_comp, MonoidHom.comp_apply]

/-- Pointwise composition law for `K2.equivOfRingEquiv`. -/
@[simp]
theorem equivOfRingEquiv_comp_apply
    {R S T : Type u} [Ring R] [Ring S] [Ring T]
    (e : R ≃+* S) (e' : S ≃+* T) (x : Additive (K2 R)) :
    K2.equivOfRingEquiv (e.trans e') x =
      K2.equivOfRingEquiv e' (K2.equivOfRingEquiv e x) := by
  rw [equivOfRingEquiv_comp]
  rfl

/-- Symmetry law for `K2.equivOfRingEquiv`: transport along `e.symm` equals
the symmetric additive equivalence. Same-universe only; no Morita, Milnor,
symbol/Matsumoto or product claim. -/
@[simp]
theorem equivOfRingEquiv_symm {R S : Type u} [Ring R] [Ring S]
    (e : R ≃+* S) :
    K2.equivOfRingEquiv e.symm = (K2.equivOfRingEquiv e).symm := by
  ext x
  apply (K2.equivOfRingEquiv e).injective
  calc
    K2.equivOfRingEquiv e (K2.equivOfRingEquiv e.symm x) =
        K2.equivOfRingEquiv (e.symm.trans e) x := by
      rw [equivOfRingEquiv_comp_apply]
    _ = x := by simp
    _ = K2.equivOfRingEquiv e ((K2.equivOfRingEquiv e).symm x) := by
      rw [AddEquiv.apply_symm_apply]

/-- Pointwise inverse law for `K2.equivOfRingEquiv`. -/
@[simp]
theorem equivOfRingEquiv_symm_apply {R S : Type u} [Ring R] [Ring S]
    (e : R ≃+* S) (x : Additive (K2 S)) :
    K2.equivOfRingEquiv e.symm x = (K2.equivOfRingEquiv e).symm x := by
  rw [equivOfRingEquiv_symm]

end K2

end AlgebraicKTheory

end
