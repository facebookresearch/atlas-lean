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

public import MathlibExt.KTheory.Milnor.ClassicalDegree
public import MathlibExt.KTheory.Milnor.DegreeMap
/-!
# Functoriality of classical degreewise Milnor K-theory

For `f : F →+* K`, the induced map `MilnorK F n →ₗ[ℤ] MilnorK K n`
and for `e : F ≃+* K` the induced linear equivalence.

Since `MilnorK F n` is definitionally `MilnorKRing.degree F n`, the
classical map is directly `MilnorKRing.mapDegree`, and the equivalence
comes from the degree-level field equivalence with composition laws
`mapDegree_id` and `mapDegree_comp`.

Ergonomic degree-generic wrappers `mapAddHom` (`→+`) and
`mapMultiplicative` (`Multiplicative _ →*`) are provided for downstream
use, in particular for tactics expecting `AddMonoidHom` / `MonoidHom`
and for the C3 Matsumoto comparison where the target is multiplicative.

## Main definitions
* `MilnorK.map`
* `MilnorK.mapAddHom`
* `MilnorK.mapMultiplicative`
* `MilnorK.mapEquiv`

## Main results
* `MilnorK.map_id`
* `MilnorK.map_comp`
* `MilnorK.map_mk`
* `MilnorK.mapAddHom_id`
* `MilnorK.mapAddHom_comp`
* `MilnorK.mapAddHom_mk`
* `MilnorK.mapMultiplicative_id`
* `MilnorK.mapMultiplicative_comp`
* `MilnorK.mapEquiv_id`
* `MilnorK.mapEquiv_comp`
* `MilnorK.mapEquiv_symm`
-/
@[expose] public section

namespace MilnorK

variable {F K L : Type*} [Field F] [Field K] [Field L]

/-- The map `MilnorK F n →ₗ[ℤ] MilnorK K n` induced by `f : F →+* K`.
Since `MilnorK F n = MilnorKRing.degree F n` definitionally, this is
`MilnorKRing.mapDegree`. -/
noncomputable def map (f : F →+* K) (n : ℕ) : MilnorK F n →ₗ[ℤ] MilnorK K n :=
  MilnorKRing.mapDegree f n

/-- Computation of `map` on `mk`. -/
@[simp]
theorem map_mk (f : F →+* K) (n : ℕ) (x : TensorRing.degree F n) :
    map f n (mk F n x) =
      mk K n (MilnorKRing.tensorMapDegree f n x) := by
  apply Subtype.ext
  simp only [map, mk_coe, MilnorKRing.mapDegree_apply,
    MilnorKRing.mkLinear_apply, MilnorKRing.map_mk,
    MilnorKRing.tensorMapDegree_coe]

/-- The identity ring homomorphism induces the identity linear map on
`MilnorK F n`. -/
@[simp]
theorem map_id (n : ℕ) : map (RingHom.id F) n = LinearMap.id :=
  MilnorKRing.mapDegree_id n

/-- Composition of ring homomorphisms induces composition of the associated
maps on `MilnorK`. -/
theorem map_comp (f : F →+* K) (g : K →+* L) (n : ℕ) :
    map (g.comp f) n = (map g n).comp (map f n) :=
  MilnorKRing.mapDegree_comp f g n

/-! ### AddMonoidHom wrapper -/

/-- The additive monoid homomorphism `MilnorK F n →+ MilnorK K n` induced by
`f : F →+* K`. This is `(map f n).toAddMonoidHom` and is provided as an
ergonomic `AddMonoidHom` wrapper for downstream rewriting and for
`mapMultiplicative`. -/
noncomputable def mapAddHom (f : F →+* K) (n : ℕ) :
    MilnorK F n →+ MilnorK K n :=
  (map f n).toAddMonoidHom

/-- Applying `mapAddHom f n` coincides with `map f n`. -/
@[simp]
theorem mapAddHom_apply (f : F →+* K) (n : ℕ) (x : MilnorK F n) :
    mapAddHom f n x = map f n x :=
  rfl

/-- Computation of `mapAddHom` on `mk`. -/
@[simp]
theorem mapAddHom_mk (f : F →+* K) (n : ℕ) (x : TensorRing.degree F n) :
    mapAddHom f n (mk F n x) =
      mk K n (MilnorKRing.tensorMapDegree f n x) := by
  calc
    mapAddHom f n (mk F n x) = map f n (mk F n x) := rfl
    _ = mk K n (MilnorKRing.tensorMapDegree f n x) := map_mk f n x

/-- The identity ring homomorphism induces the identity `AddMonoidHom` on
`MilnorK F n`. -/
@[simp]
theorem mapAddHom_id (n : ℕ) :
    mapAddHom (RingHom.id F) n = AddMonoidHom.id (MilnorK F n) := by
  calc
    mapAddHom (RingHom.id F) n = (map (RingHom.id F) n).toAddMonoidHom := rfl
    _ = (LinearMap.id : MilnorK F n →ₗ[ℤ] MilnorK F n).toAddMonoidHom := by
      rw [map_id]
    _ = AddMonoidHom.id (MilnorK F n) := rfl

/-- Composition of ring homomorphisms induces composition of the associated
`AddMonoidHom`s on `MilnorK`. -/
theorem mapAddHom_comp (f : F →+* K) (g : K →+* L) (n : ℕ) :
    mapAddHom (g.comp f) n =
      (mapAddHom g n).comp (mapAddHom f n) := by
  calc
    mapAddHom (g.comp f) n = (map (g.comp f) n).toAddMonoidHom := rfl
    _ = ((map g n).comp (map f n)).toAddMonoidHom := by rw [map_comp]
    _ = (map g n).toAddMonoidHom.comp (map f n).toAddMonoidHom := rfl
    _ = (mapAddHom g n).comp (mapAddHom f n) := rfl

/-- Pointwise composition for `mapAddHom`. -/
@[simp]
theorem mapAddHom_comp_apply (f : F →+* K) (g : K →+* L) (n : ℕ)
    (x : MilnorK F n) :
    mapAddHom (g.comp f) n x =
      mapAddHom g n (mapAddHom f n x) := by
  calc
    mapAddHom (g.comp f) n x =
        ((mapAddHom g n).comp (mapAddHom f n)) x := by
      rw [mapAddHom_comp]
    _ = mapAddHom g n (mapAddHom f n x) := rfl

/-! ### Multiplicative wrapper -/

/-- The monoid homomorphism on `Multiplicative` induced by `f : F →+* K`.
This is `AddMonoidHom.toMultiplicative (mapAddHom f n)` and is provided for
downstream use where the target is multiplicative, e.g. the C3 Matsumoto
comparison. -/
noncomputable def mapMultiplicative (f : F →+* K) (n : ℕ) :
    Multiplicative (MilnorK F n) →* Multiplicative (MilnorK K n) :=
  AddMonoidHom.toMultiplicative (mapAddHom f n)

/-- The underlying additive value of `mapMultiplicative` is `mapAddHom`. -/
@[simp]
theorem mapMultiplicative_toAdd (f : F →+* K) (n : ℕ)
    (x : Multiplicative (MilnorK F n)) :
    (mapMultiplicative f n x).toAdd = mapAddHom f n x.toAdd :=
  rfl

/-- `mapMultiplicative` on `ofAdd`. -/
@[simp]
theorem mapMultiplicative_ofAdd (f : F →+* K) (n : ℕ)
    (x : MilnorK F n) :
    mapMultiplicative f n (Multiplicative.ofAdd x) =
      Multiplicative.ofAdd (mapAddHom f n x) :=
  rfl

/-- Computation of `mapMultiplicative` on `ofAdd (mk ...)`. -/
@[simp]
theorem mapMultiplicative_ofAdd_mk (f : F →+* K) (n : ℕ)
    (x : TensorRing.degree F n) :
    mapMultiplicative f n (Multiplicative.ofAdd (mk F n x)) =
      Multiplicative.ofAdd (mk K n (MilnorKRing.tensorMapDegree f n x)) := by
  calc
    mapMultiplicative f n (Multiplicative.ofAdd (mk F n x)) =
        Multiplicative.ofAdd (mapAddHom f n (mk F n x)) :=
      rfl
    _ = Multiplicative.ofAdd (mk K n (MilnorKRing.tensorMapDegree f n x)) := by
      rw [mapAddHom_mk]

/-- Alternate form of `mapMultiplicative` computation via `map_mk`. -/
theorem mapMultiplicative_ofAdd_mk_eq_map_mk (f : F →+* K) (n : ℕ)
    (x : TensorRing.degree F n) :
    mapMultiplicative f n (Multiplicative.ofAdd (mk F n x)) =
      Multiplicative.ofAdd (map f n (mk F n x)) := by
  calc
    mapMultiplicative f n (Multiplicative.ofAdd (mk F n x)) =
        Multiplicative.ofAdd (mapAddHom f n (mk F n x)) :=
      rfl
    _ = Multiplicative.ofAdd (map f n (mk F n x)) := rfl

/-- The identity ring homomorphism induces the identity `MonoidHom` on
`Multiplicative (MilnorK F n)`. -/
@[simp]
theorem mapMultiplicative_id (n : ℕ) :
    mapMultiplicative (RingHom.id F) n =
      MonoidHom.id (Multiplicative (MilnorK F n)) := by
  apply MonoidHom.ext
  intro x
  calc
    mapMultiplicative (RingHom.id F) n x =
        Multiplicative.ofAdd (mapAddHom (RingHom.id F) n x.toAdd) :=
      rfl
    _ = Multiplicative.ofAdd (AddMonoidHom.id (MilnorK F n) x.toAdd) := by
      rw [mapAddHom_id]
    _ = Multiplicative.ofAdd x.toAdd := rfl
    _ = x := rfl

/-- Composition of ring homomorphisms induces composition of the associated
`MonoidHom`s on `Multiplicative (MilnorK)`. -/
theorem mapMultiplicative_comp (f : F →+* K) (g : K →+* L) (n : ℕ) :
    mapMultiplicative (g.comp f) n =
      (mapMultiplicative g n).comp (mapMultiplicative f n) := by
  apply MonoidHom.ext
  intro x
  calc
    mapMultiplicative (g.comp f) n x =
        Multiplicative.ofAdd (mapAddHom (g.comp f) n x.toAdd) :=
      rfl
    _ = Multiplicative.ofAdd (mapAddHom g n (mapAddHom f n x.toAdd)) := by
      rw [mapAddHom_comp_apply]
    _ = mapMultiplicative g n
        (Multiplicative.ofAdd (mapAddHom f n x.toAdd)) :=
      rfl
    _ = mapMultiplicative g n (mapMultiplicative f n x) := rfl

/-- Pointwise composition for `mapMultiplicative`. -/
@[simp]
theorem mapMultiplicative_comp_apply (f : F →+* K) (g : K →+* L) (n : ℕ)
    (x : Multiplicative (MilnorK F n)) :
    mapMultiplicative (g.comp f) n x =
      mapMultiplicative g n (mapMultiplicative f n x) := by
  calc
    mapMultiplicative (g.comp f) n x =
        ((mapMultiplicative g n).comp (mapMultiplicative f n)) x := by
      rw [mapMultiplicative_comp]
    _ = mapMultiplicative g n (mapMultiplicative f n x) := rfl

/-- `mapMultiplicative` agrees with `map` after stripping `Multiplicative`. -/
theorem mapMultiplicative_toAdd_eq_map (f : F →+* K) (n : ℕ)
    (x : Multiplicative (MilnorK F n)) :
    (mapMultiplicative f n x).toAdd = map f n x.toAdd := by
  simp only [mapMultiplicative_toAdd, mapAddHom_apply]

/-- `mapMultiplicative` on `ofAdd` agrees with `map`. -/
theorem mapMultiplicative_ofAdd_eq_map (f : F →+* K) (n : ℕ)
    (x : MilnorK F n) :
    mapMultiplicative f n (Multiplicative.ofAdd x) =
      Multiplicative.ofAdd (map f n x) := by
  simp only [mapMultiplicative_ofAdd, mapAddHom_apply]

/-! ### Linear equivalence for field equivalences -/

/-- The linear equivalence `MilnorK F n ≃ₗ[ℤ] MilnorK K n` induced by `e : F ≃+* K`.
Built from `map` with `map_id` and `map_comp`. -/
noncomputable def mapEquiv (e : F ≃+* K) (n : ℕ) :
    MilnorK F n ≃ₗ[ℤ] MilnorK K n :=
  LinearEquiv.ofLinearMap (map e.toRingHom n) (map e.symm.toRingHom n)
    (by
      have hcomp : e.toRingHom.comp e.symm.toRingHom = RingHom.id K := by
        ext x
        simp
      have h : map e.toRingHom n ∘ₗ map e.symm.toRingHom n = LinearMap.id := by
        calc
          map e.toRingHom n ∘ₗ map e.symm.toRingHom n
              = map (e.toRingHom.comp e.symm.toRingHom) n := by
                rw [← map_comp]
          _ = map (RingHom.id K) n := by rw [hcomp]
          _ = LinearMap.id := map_id n
      exact h)
    (by
      have hcomp : e.symm.toRingHom.comp e.toRingHom = RingHom.id F := by
        ext x
        simp
      have h : map e.symm.toRingHom n ∘ₗ map e.toRingHom n = LinearMap.id := by
        calc
          map e.symm.toRingHom n ∘ₗ map e.toRingHom n
              = map (e.symm.toRingHom.comp e.toRingHom) n := by
                rw [← map_comp]
          _ = map (RingHom.id F) n := by rw [hcomp]
          _ = LinearMap.id := map_id n
      exact h)

/-- The underlying linear map of `mapEquiv` is `map` for the underlying
ring homomorphism. -/
@[simp]
theorem mapEquiv_toLinearMap (e : F ≃+* K) (n : ℕ) :
    (mapEquiv e n).toLinearMap = map e.toRingHom n :=
  rfl

/-- Applying `mapEquiv` is the same as applying `map` for the underlying ring
homomorphism. -/
@[simp]
theorem mapEquiv_apply (e : F ≃+* K) (n : ℕ) (x : MilnorK F n) :
    mapEquiv e n x = map e.toRingHom n x :=
  rfl

/-- The identity field equivalence induces the identity linear equivalence. -/
@[simp]
theorem mapEquiv_id (F : Type*) [Field F] (n : ℕ) :
    mapEquiv (RingEquiv.refl F) n = LinearEquiv.refl ℤ (MilnorK F n) := by
  apply LinearEquiv.ext
  intro x
  change map (RingHom.id F) n x = x
  rw [map_id]
  rfl

/-- Field-equivalence maps preserve forward composition. -/
theorem mapEquiv_comp (e : F ≃+* K) (e' : K ≃+* L) (n : ℕ) :
    mapEquiv (e.trans e') n = (mapEquiv e n).trans (mapEquiv e' n) := by
  apply LinearEquiv.ext
  intro x
  change map (e'.toRingHom.comp e.toRingHom) n x =
    map e'.toRingHom n (map e.toRingHom n x)
  rw [map_comp, LinearMap.comp_apply]

/-- The inverse of `mapEquiv e` is `mapEquiv` for the inverse field equivalence. -/
@[simp]
theorem mapEquiv_symm (e : F ≃+* K) (n : ℕ) :
    (mapEquiv e n).symm = mapEquiv e.symm n := by
  apply LinearEquiv.ext
  intro x
  apply (mapEquiv e n).injective
  calc
    mapEquiv e n ((mapEquiv e n).symm x) = x := by
      rw [LinearEquiv.apply_symm_apply]
    _ = mapEquiv (e.symm.trans e) n x := by simp
    _ = mapEquiv e n (mapEquiv e.symm n x) := by
      rw [mapEquiv_comp]
      rfl

/-- Applying the inverse of `mapEquiv` coincides with `map` for the inverse
equivalence. -/
@[simp]
theorem mapEquiv_symm_apply (e : F ≃+* K) (n : ℕ) (x : MilnorK K n) :
    (mapEquiv e n).symm x = map e.symm.toRingHom n x :=
  rfl

end MilnorK
