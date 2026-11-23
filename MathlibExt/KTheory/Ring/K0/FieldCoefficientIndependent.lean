/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.Comparison.ScalarExtensionK0Coefficients
public import MathlibExt.KTheory.Ring.K0.FieldCoefficient

/-!
# Native field coefficient naturality in independent universes

The original additive map `FGProjectiveCat.scalarExtensionK0` preserves the
integer coefficient of every algebraic field K₀ class, with the source and
target field universes independent. The existing rank equivalences recover
its whole map and its coefficient inverse, and show that this actual map is
bijective. Its actual native projective image preserves finite dimension.

The original `RingK0` carriers and scalar-extension map are retained.

## References

* Weibel, *The K-book*, Chapter II, §2, p.68: algebraic field K₀ and
  scalar-extension functoriality.
-/

@[expose] public section

noncomputable section

universe uF uG

namespace AlgebraicKTheory.RingK0

variable {F : Type uF} {G : Type uG} [Field F] [Field G]

/-- Field rank is natural for the original scalar-extension map, retaining
both native K₀ carriers in independent universes. -/
theorem fieldRank_scalarExtensionK0 (f : F →+* G) :
    (fieldRank G).toAddMonoidHom.comp (FGProjectiveCat.scalarExtensionK0 f) =
      (fieldRank F).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro x
  change fieldRank G (FGProjectiveCat.scalarExtensionK0 f x) = fieldRank F x
  calc
    fieldRank G (FGProjectiveCat.scalarExtensionK0 f x) =
        fieldRank G
          (FGProjectiveCat.scalarExtensionK0 f (fieldRank F x : RingK0 F)) :=
      congrArg (fun y => fieldRank G (FGProjectiveCat.scalarExtensionK0 f y))
        (intCast_fieldRank F x).symm
    _ = fieldRank F x := by
      rw [FGProjectiveCat.scalarExtensionK0_intCast]
      exact map_intCast (fieldRank G) _

/-- The original native scalar-extension map preserves the coefficient of
each virtual projective class. -/
@[simp]
theorem fieldRank_scalarExtensionK0_apply (f : F →+* G) (x : RingK0 F) :
    fieldRank G (FGProjectiveCat.scalarExtensionK0 f x) = fieldRank F x :=
  DFunLike.congr_fun (fieldRank_scalarExtensionK0 f) x

/-- The existing field coefficient equivalences and their actual inverse
recover the entire original additive scalar-extension map. -/
theorem scalarExtensionK0_eq_fieldRank (f : F →+* G) :
    FGProjectiveCat.scalarExtensionK0 f =
      (fieldRankEquiv G).symm.toAddMonoidHom.comp (fieldRankEquiv F).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro x
  change FGProjectiveCat.scalarExtensionK0 f x = (fieldRank F x : RingK0 G)
  calc
    FGProjectiveCat.scalarExtensionK0 f x =
        FGProjectiveCat.scalarExtensionK0 f (fieldRank F x : RingK0 F) :=
      congrArg (FGProjectiveCat.scalarExtensionK0 f) (intCast_fieldRank F x).symm
    _ = (fieldRank F x : RingK0 G) := FGProjectiveCat.scalarExtensionK0_intCast f _

/-- The whole integer-cast inverse is compatible with the original native
scalar-extension map. -/
theorem scalarExtensionK0_fieldRankEquiv_symm (f : F →+* G) :
    (FGProjectiveCat.scalarExtensionK0 f).comp (fieldRankEquiv F).symm.toAddMonoidHom =
      (fieldRankEquiv G).symm.toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro z
  change FGProjectiveCat.scalarExtensionK0 f (z : RingK0 F) = (z : RingK0 G)
  exact FGProjectiveCat.scalarExtensionK0_intCast f z

/-- Under the existing coefficient equivalences, the whole original field
scalar-extension map is the identity on ℤ. -/
theorem scalarExtensionK0_coefficient_dictionary (f : F →+* G) :
    ((fieldRankEquiv G).toAddMonoidHom.comp
        (FGProjectiveCat.scalarExtensionK0 f)).comp
      (fieldRankEquiv F).symm.toAddMonoidHom = AddMonoidHom.id ℤ := by
  apply AddMonoidHom.ext
  intro z
  change fieldRank G (FGProjectiveCat.scalarExtensionK0 f (z : RingK0 F)) = z
  rw [FGProjectiveCat.scalarExtensionK0_intCast]
  exact map_intCast (fieldRank G) z

/-- An actual projective generator retains its source dimension as the
coefficient of its original native scalar-extension image. -/
theorem fieldRank_scalarExtensionK0_mk (f : F →+* G) (P : FGProjectiveCat.{uF} F) :
    fieldRank G (FGProjectiveCat.scalarExtensionK0 f (K0.mk P)) =
      (Module.finrank F P : ℤ) :=
  (fieldRank_scalarExtensionK0_apply f (K0.mk P)).trans (fieldRank_mk F P)

/-- The original scalar-extension map between field K₀ groups is bijective,
with no inverse field homomorphism or finite extension-degree premise. -/
theorem scalarExtensionK0_bijective_of_field (f : F →+* G) :
    Function.Bijective (FGProjectiveCat.scalarExtensionK0 f) := by
  rw [scalarExtensionK0_eq_fieldRank f]
  exact ((fieldRankEquiv F).toAddEquiv.trans (fieldRankEquiv G).symm.toAddEquiv).bijective

end AlgebraicKTheory.RingK0

namespace FGProjectiveCat

open AlgebraicKTheory

variable {F : Type uF} {G : Type uG} [Field F] [Field G]

/-- The actual native projective object of scalar extension preserves finite
field dimension, including its existing shrink coordinates. -/
theorem finrank_ringScalarExtension (f : F →+* G) (P : FGProjectiveCat.{uF} F) :
    Module.finrank G ((ringScalarExtension f).obj P) = Module.finrank F P := by
  have h := RingK0.fieldRank_scalarExtensionK0_mk f P
  rw [scalarExtensionK0_mk, RingK0.fieldRank_mk] at h
  exact_mod_cast h

end FGProjectiveCat
