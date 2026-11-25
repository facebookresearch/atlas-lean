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

public import MathlibExt.KTheory.Exact.K0.Functor
public import Mathlib.CategoryTheory.Equivalence
public import MathlibExt.KTheory.Exact.K0.MapRing

@[expose] public section

open CategoryTheory Limits

universe v₁ u₁ v₂ u₂

namespace AlgebraicKTheory

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]

/-- `K₀` is invariant under exact equivalence: an equivalence of categories whose
functor and inverse are additive and exact induces an additive equivalence on `K₀`.

The construction uses `K0.map` in both directions; the inverse identities follow
from `K0.map_comp`, `K0.map_eq_of_iso`, `K0.map_id` and the unit/counit
natural isomorphisms of the equivalence. -/
noncomputable def K0.equivOfEquivalence (e : C ≌ D)
    [e.functor.Additive] [e.inverse.Additive] [e.functor.IsExact] [e.inverse.IsExact] :
    K0 C ≃+ K0 D where
  toFun := K0.map e.functor
  invFun := K0.map e.inverse
  left_inv x := by
    have h : (K0.map e.inverse).comp (K0.map e.functor) = AddMonoidHom.id (K0 C) := by
      calc
        (K0.map e.inverse).comp (K0.map e.functor)
            = K0.map (e.functor ⋙ e.inverse) := (K0.map_comp e.functor e.inverse).symm
        _ = K0.map (𝟭 C) := K0.map_eq_of_iso e.unitIso.symm
        _ = AddMonoidHom.id (K0 C) := K0.map_id
    calc
      K0.map e.inverse (K0.map e.functor x)
          = ((K0.map e.inverse).comp (K0.map e.functor)) x := rfl
      _ = (AddMonoidHom.id (K0 C)) x := by rw [h]
      _ = x := rfl
  right_inv x := by
    have h : (K0.map e.functor).comp (K0.map e.inverse) = AddMonoidHom.id (K0 D) := by
      calc
        (K0.map e.functor).comp (K0.map e.inverse)
            = K0.map (e.inverse ⋙ e.functor) := (K0.map_comp e.inverse e.functor).symm
        _ = K0.map (𝟭 D) := K0.map_eq_of_iso e.counitIso
        _ = AddMonoidHom.id (K0 D) := K0.map_id
    calc
      K0.map e.functor (K0.map e.inverse x)
          = ((K0.map e.functor).comp (K0.map e.inverse)) x := rfl
      _ = (AddMonoidHom.id (K0 D)) x := by rw [h]
      _ = x := rfl
  map_add' := map_add _

@[simp]
lemma K0.equivOfEquivalence_mk (e : C ≌ D)
    [e.functor.Additive] [e.inverse.Additive] [e.functor.IsExact] [e.inverse.IsExact]
    (X : C) :
    K0.equivOfEquivalence e (K0.mk X) = K0.mk (e.functor.obj X) := by
  simp [K0.equivOfEquivalence]

section Monoidal

variable [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C]
  [ExactCategory.IsTensorBiexact C]
variable [MonoidalCategory D] [BraidedCategory D] [MonoidalPreadditive D]
  [ExactCategory.IsTensorBiexact D]

/-- An exact additive equivalence whose forward functor is strong monoidal
induces a ring equivalence on `K₀`.

The forward and inverse functions are the original additive `K₀` maps of
`K0.equivOfEquivalence`. Only the forward functor needs a monoidal structure;
multiplication is supplied by the existing `K0.mapRing`. -/
noncomputable def K0.ringEquivOfEquivalence (e : C ≌ D)
    [e.functor.Additive] [e.inverse.Additive] [e.functor.IsExact] [e.inverse.IsExact]
    [e.functor.Monoidal] : K0 C ≃+* K0 D :=
  { K0.equivOfEquivalence e with
    map_mul' := fun x y => map_mul (K0.mapRing e.functor) x y }

/-- Forgetting multiplication retains the original exact additive equivalence. -/
@[simp]
lemma K0.ringEquivOfEquivalence_toAddEquiv (e : C ≌ D)
    [e.functor.Additive] [e.inverse.Additive] [e.functor.IsExact] [e.inverse.IsExact]
    [e.functor.Monoidal] :
    (K0.ringEquivOfEquivalence e : K0 C ≃+ K0 D) = K0.equivOfEquivalence e :=
  rfl

/-- The forward ring homomorphism is the existing strong monoidal exact `K₀` map. -/
@[simp]
lemma K0.ringEquivOfEquivalence_toRingHom (e : C ≌ D)
    [e.functor.Additive] [e.inverse.Additive] [e.functor.IsExact] [e.inverse.IsExact]
    [e.functor.Monoidal] :
    (K0.ringEquivOfEquivalence e : K0 C →+* K0 D) = K0.mapRing e.functor := by
  ext x
  rfl

/-- The forward ring equivalence retains the original object generators. -/
@[simp]
lemma K0.ringEquivOfEquivalence_mk (e : C ≌ D)
    [e.functor.Additive] [e.inverse.Additive] [e.functor.IsExact] [e.inverse.IsExact]
    [e.functor.Monoidal] (X : C) :
    K0.ringEquivOfEquivalence e (K0.mk X) = K0.mk (e.functor.obj X) :=
  K0.equivOfEquivalence_mk e X

/-- The inverse ring equivalence uses the original inverse functor on generators. -/
@[simp]
lemma K0.ringEquivOfEquivalence_symm_mk (e : C ≌ D)
    [e.functor.Additive] [e.inverse.Additive] [e.functor.IsExact] [e.inverse.IsExact]
    [e.functor.Monoidal] (Y : D) :
    (K0.ringEquivOfEquivalence e).symm (K0.mk Y) = K0.mk (e.inverse.obj Y) :=
  K0.map_mk e.inverse Y

end Monoidal

end AlgebraicKTheory
