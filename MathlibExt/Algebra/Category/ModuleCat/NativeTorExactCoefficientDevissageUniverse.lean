/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.NativeTorFiniteLengthDevissageUniverse
public import MathlibExt.Algebra.Category.ModuleCat.FlatHomology

/-!
# Native Euler devissage for actual extended and restricted coefficients

Flat scalar extension to Q followed by restriction along the actual map S→Q
preserves the original short exact coefficient rows. Only the map into Q from
the original local ring is required to be flat. The native long exact sequence
then earns finite lengths, the residue cutoff, and the actual Euler multiplier.
The generic exact additive functor engine uses actual composition-series rows.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct ModuleCat.UniverseTensor ZeroObject

universe u v w x

namespace ModuleCat

namespace UniverseTensor

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [IsLocalRing R]

/-- The exact coefficient devissage theorem for literal native Tor in the first variable. -/
theorem nativeTorFiniteLength_devissage_first_of_preservesHomology
    (F : ModuleCat.{max u v w} R ⥤ ModuleCat.{max u v w} S)
    [F.Additive] [F.PreservesHomology] (M : ModuleCat.{max u v w} S)
    (N : Type (max u v w)) [AddCommGroup N] [Module R N] (hN : IsFiniteLength R N)
    (cutoff : ℕ)
    (hκ : ∀ q < cutoff,
      Module.length S (((@Tor (ModuleCat.{max u v w} S) inferInstance
        (monoidalCategory.{v, max u w}) inferInstance (monoidalPreadditive.{v, max u w})
        inferInstance q).obj (F.obj (nativeResidueCoefficient.{u, max v w} R))).obj M) ≠ ⊤)
    (hzκ : ∀ q, cutoff ≤ q → IsZero (((@Tor (ModuleCat.{max u v w} S) inferInstance
      (monoidalCategory.{v, max u w}) inferInstance (monoidalPreadditive.{v, max u w})
      inferInstance q).obj (F.obj (nativeResidueCoefficient.{u, max v w} R))).obj M)) :
    (∀ q < cutoff, Module.length S (((@Tor (ModuleCat.{max u v w} S) inferInstance
      (monoidalCategory.{v, max u w}) inferInstance (monoidalPreadditive.{v, max u w})
      inferInstance q).obj (F.obj (ModuleCat.of R N))).obj M) ≠ ⊤) ∧
    (∀ q, cutoff ≤ q → IsZero (((@Tor (ModuleCat.{max u v w} S) inferInstance
      (monoidalCategory.{v, max u w}) inferInstance (monoidalPreadditive.{v, max u w})
      inferInstance q).obj (F.obj (ModuleCat.of R N))).obj M)) ∧
    rawNativeTorEulerSum.{v, max u w} S (F.obj (ModuleCat.of R N)) M cutoff =
      ((Module.length R N).toNat : ℤ) * rawNativeTorEulerSum.{v, max u w} S
        (F.obj (nativeResidueCoefficient.{u, max v w} R)) M cutoff := by
  let : MonoidalCategoryStruct (ModuleCat.{max u v w} S) := tensorStructure.{v, max u w}
  let : MonoidalCategory (ModuleCat.{max u v w} S) := monoidalCategory.{v, max u w}
  let : MonoidalPreadditive (ModuleCat.{max u v w} S) := monoidalPreadditive.{v, max u w}
  let k := nativeResidueCoefficient.{u, max v w} R
  have h := nativeTorFiniteLength_devissage_of_preservesHomology.{u, v, w} R S F M N hN
    cutoff (fun q hq => by rw [nativeTor_length_symm.{v, max u w} S M (F.obj k) q]; exact hκ q hq)
    (fun q hq => (hzκ q hq).of_iso (nativeTorSymmetry.{v, max u w} S M (F.obj k) q))
  constructor
  · intro q hq
    rw [nativeTor_length_symm.{v, max u w} S (F.obj (ModuleCat.of R N)) M q]
    exact h.1 q hq
  constructor
  · intro q hq
    exact (h.2.1 q hq).of_iso (nativeTorSymmetry.{v, max u w} S (F.obj (ModuleCat.of R N)) M q)
  · rw [rawNativeTorEulerSum_symm.{v, max u w} S (F.obj (ModuleCat.of R N)) M cutoff,
      rawNativeTorEulerSum_symm.{v, max u w} S (F.obj k) M cutoff]
    exact h.2.2

/-- Actual extended and restricted coefficients inherit the residue cutoff and native Euler sum. -/
theorem nativeTorFiniteLength_extendRestrict_devissage
    (Q : Type w) [CommRing Q] (f : R →+* Q) (g : S →+* Q) (hf : f.Flat)
    (M : ModuleCat.{max u v w x} S) (N : Type (max u v w x))
    [AddCommGroup N] [Module R N] (hN : IsFiniteLength R N) (cutoff : ℕ) :
    let F : ModuleCat.{max u v w x} R ⥤ ModuleCat.{max u v w x} S :=
      extendScalars.{u, w, max u v w x} f ⋙ restrictScalars.{max u v w x, v, w} g
    (∀ q < cutoff, Module.length S (((@Tor (ModuleCat.{max u v w x} S) inferInstance
      (monoidalCategory.{v, max u w x}) inferInstance
      (monoidalPreadditive.{v, max u w x}) inferInstance q).obj M).obj
        (F.obj (nativeResidueCoefficient.{u, max v w x} R))) ≠ ⊤) →
    (∀ q, cutoff ≤ q → IsZero (((@Tor (ModuleCat.{max u v w x} S) inferInstance
      (monoidalCategory.{v, max u w x}) inferInstance
      (monoidalPreadditive.{v, max u w x}) inferInstance q).obj M).obj
        (F.obj (nativeResidueCoefficient.{u, max v w x} R)))) →
    (∀ q < cutoff, Module.length S (((@Tor (ModuleCat.{max u v w x} S) inferInstance
      (monoidalCategory.{v, max u w x}) inferInstance
      (monoidalPreadditive.{v, max u w x}) inferInstance q).obj M).obj
        (F.obj (ModuleCat.of R N))) ≠ ⊤) ∧
    (∀ q, cutoff ≤ q → IsZero (((@Tor (ModuleCat.{max u v w x} S) inferInstance
      (monoidalCategory.{v, max u w x}) inferInstance
      (monoidalPreadditive.{v, max u w x}) inferInstance q).obj M).obj
        (F.obj (ModuleCat.of R N)))) ∧
    rawNativeTorEulerSum.{v, max u w x} S M (F.obj (ModuleCat.of R N)) cutoff =
      ((Module.length R N).toNat : ℤ) * rawNativeTorEulerSum.{v, max u w x} S M
        (F.obj (nativeResidueCoefficient.{u, max v w x} R)) cutoff := by
  dsimp only
  intro hκ hzκ
  let F : ModuleCat.{max u v w x} R ⥤ ModuleCat.{max u v w x} S :=
    extendScalars.{u, w, max u v w x} f ⋙ restrictScalars.{max u v w x, v, w} g
  have : F.PreservesHomology := preservesHomology_extendScalars_restrictScalars_of_flat f g hf
  exact nativeTorFiniteLength_devissage_of_preservesHomology.{u, v, max w x}
    R S F M N hN cutoff hκ hzκ

/-- Actual extended and restricted coefficients satisfy devissage in the first native variable. -/
theorem nativeTorFiniteLength_extendRestrict_devissage_first
    (Q : Type w) [CommRing Q] (f : R →+* Q) (g : S →+* Q) (hf : f.Flat)
    (M : ModuleCat.{max u v w x} S) (N : Type (max u v w x))
    [AddCommGroup N] [Module R N] (hN : IsFiniteLength R N) (cutoff : ℕ) :
    let F : ModuleCat.{max u v w x} R ⥤ ModuleCat.{max u v w x} S :=
      extendScalars.{u, w, max u v w x} f ⋙ restrictScalars.{max u v w x, v, w} g
    (∀ q < cutoff, Module.length S (((@Tor (ModuleCat.{max u v w x} S) inferInstance
      (monoidalCategory.{v, max u w x}) inferInstance
      (monoidalPreadditive.{v, max u w x}) inferInstance q).obj
        (F.obj (nativeResidueCoefficient.{u, max v w x} R))).obj M) ≠ ⊤) →
    (∀ q, cutoff ≤ q → IsZero (((@Tor (ModuleCat.{max u v w x} S) inferInstance
      (monoidalCategory.{v, max u w x}) inferInstance
      (monoidalPreadditive.{v, max u w x}) inferInstance q).obj
        (F.obj (nativeResidueCoefficient.{u, max v w x} R))).obj M)) →
    (∀ q < cutoff, Module.length S (((@Tor (ModuleCat.{max u v w x} S) inferInstance
      (monoidalCategory.{v, max u w x}) inferInstance
      (monoidalPreadditive.{v, max u w x}) inferInstance q).obj
        (F.obj (ModuleCat.of R N))).obj M) ≠ ⊤) ∧
    (∀ q, cutoff ≤ q → IsZero (((@Tor (ModuleCat.{max u v w x} S) inferInstance
      (monoidalCategory.{v, max u w x}) inferInstance
      (monoidalPreadditive.{v, max u w x}) inferInstance q).obj
        (F.obj (ModuleCat.of R N))).obj M)) ∧
    rawNativeTorEulerSum.{v, max u w x} S (F.obj (ModuleCat.of R N)) M cutoff =
      ((Module.length R N).toNat : ℤ) * rawNativeTorEulerSum.{v, max u w x} S
        (F.obj (nativeResidueCoefficient.{u, max v w x} R)) M cutoff := by
  dsimp only
  intro hκ hzκ
  let F : ModuleCat.{max u v w x} R ⥤ ModuleCat.{max u v w x} S :=
    extendScalars.{u, w, max u v w x} f ⋙ restrictScalars.{max u v w x, v, w} g
  have : F.PreservesHomology := preservesHomology_extendScalars_restrictScalars_of_flat f g hf
  exact nativeTorFiniteLength_devissage_first_of_preservesHomology.{u, v, max w x}
    R S F M N hN cutoff hκ hzκ

end UniverseTensor
end ModuleCat
