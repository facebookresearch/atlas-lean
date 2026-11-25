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

public import MathlibExt.Analysis.CStarAlgebra.IdealQuotient
import MathlibExt.Analysis.InnerProductSpace.CompactOperator
public import MathlibExt.Analysis.Normed.Operator.Compact.Calkin
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# The C-star Calkin algebra

For a complete complex Hilbert space, compact endomorphisms are closed under
adjoint. They therefore form a closed two-sided star ideal, and the existing
Banach-space Calkin quotient inherits the canonical C-star structure. The
carrier, quotient norm, multiplication, unit, scalar action, and unital class
map are those of `CalkinAlgebra`; no second quotient is introduced.

The quotient may be the zero ring in finite dimension, so no nontriviality or
`NormOneClass` instance is asserted.
-/

@[expose] public section

noncomputable section

open NonUnitalSubalgebra
open scoped InnerProduct

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- **Adjoints preserve compact operators.** Let `H` be a complete complex Hilbert space. Its Calkin
algebra is the quotient `B(H)/K(H)` of bounded operators by compact operators, with the quotient
C*-norm. If a bounded operator on `H` is compact, its adjoint is compact. -/
theorem compactEndomorphismIdeal_star_closed {T : H →L[ℂ] H}
    (hT : T ∈ compactEndomorphismIdeal (𝕜 := ℂ) (E := H)) :
    star T ∈ compactEndomorphismIdeal (𝕜 := ℂ) (E := H) := by
  rw [mem_compactEndomorphismIdeal] at hT ⊢
  rw [ContinuousLinearMap.star_eq_adjoint]
  exact hT.adjoint

/-- **Compact operators as a closed star ideal.** Let `H` be a complete complex Hilbert space. Its
Calkin algebra is the quotient `B(H)/K(H)` of bounded operators by compact operators, with the
quotient C*-norm. The compact operators form a closed two-sided star ideal of `B(H)`. -/
def compactEndomorphismClosedStarIdeal : ClosedStarIdeal (H →L[ℂ] H) where
  carrier :=
    { compactEndomorphismIdeal (𝕜 := ℂ) (E := H) with
      star_mem' := compactEndomorphismIdeal_star_closed }
  isTwoSided := by
    constructor
    · intro a x hx
      exact NonUnitalSubalgebra.IsTwoSided.mul_mem_left a hx
    · intro x hx a
      exact NonUnitalSubalgebra.IsTwoSided.mul_mem_right hx a
  isClosed := compactEndomorphismIdeal_isClosed

@[simp]
theorem compactEndomorphismClosedStarIdeal_toNonUnitalSubalgebra :
    (compactEndomorphismClosedStarIdeal (H := H)).carrier.toNonUnitalSubalgebra =
      compactEndomorphismIdeal (𝕜 := ℂ) (E := H) :=
  rfl

@[simp]
theorem compactEndomorphismClosedStarIdeal_toSubmodule :
    (compactEndomorphismClosedStarIdeal (H := H)).carrier.toSubmodule =
      compactOperator (RingHom.id ℂ) H H :=
  rfl

namespace CalkinAlgebra

/-- **Closed-ideal description of the Calkin carrier.** Let `H` be a complete complex Hilbert space. Its
Calkin algebra is the quotient `B(H)/K(H)` of bounded operators by compact operators, with the
quotient C*-norm. The Calkin carrier equals the quotient by the closed star ideal of compact
endomorphisms. -/
theorem eq_compactEndomorphismClosedStarIdeal_quotient :
    CalkinAlgebra ℂ H =
      (compactEndomorphismClosedStarIdeal (H := H)).Quotient :=
  rfl

/-- The canonical C-star structure on the existing Calkin carrier. Its normed
ring and normed algebra parents are the pre-existing quotient structures; the
star and C-star data come from the canonical closed-star-ideal quotient. -/
noncomputable instance instCStarAlgebra : CStarAlgebra (CalkinAlgebra ℂ H) := by
  let I := compactEndomorphismClosedStarIdeal (H := H)
  let hCStar : CStarAlgebra (CalkinAlgebra ℂ H) :=
    I.unitalQuotientCStarAlgebra
  exact
    { toNormedRing := CalkinAlgebra.instNormedRing
      toStarRing := hCStar.toStarRing
      toCompleteSpace := hCStar.toCompleteSpace
      toCStarRing := hCStar.toCStarRing
      toNormedAlgebra := CalkinAlgebra.instNormedAlgebra
      toStarModule := hCStar.toStarModule }

/-- **Adjoint of an operator class.** Let `H` be a complete complex Hilbert space. Its Calkin algebra is
the quotient `B(H)/K(H)` of bounded operators by compact operators, with the quotient C*-norm. For
every bounded operator `T`, the class of `T*` equals the involution of the class of `T`. -/
@[simp]
theorem classMap_star (T : H →L[ℂ] H) :
    classMap (𝕜 := ℂ) (E := H) (star T) =
      star (classMap (𝕜 := ℂ) (E := H) T) :=
  rfl

/-- **Unital star projection to the Calkin algebra.** Let `H` be a complete complex Hilbert space. Its
Calkin algebra is the quotient `B(H)/K(H)` of bounded operators by compact operators, with the
quotient C*-norm. The quotient projection `T ↦ [T]` is a continuous unital complex star-algebra
homomorphism. -/
def classStarMap : (H →L[ℂ] H) →⋆ₐ[ℂ] CalkinAlgebra ℂ H where
  toAlgHom := (classMap (𝕜 := ℂ) (E := H)).toAlgHom
  map_star' := classMap_star

/-- **Representative formula for the star class map.** Let `H` be a complete complex Hilbert space. Its
Calkin algebra is the quotient `B(H)/K(H)` of bounded operators by compact operators, with the
quotient C*-norm. For each bounded operator `T`, the star class map is its vector-space quotient
class `[T]` modulo compact operators. -/
theorem classStarMap_apply (T : H →L[ℂ] H) :
    classStarMap (H := H) T = Submodule.Quotient.mk T :=
  rfl

/-- **Agreement of the Calkin class maps.** Let `H` be a complete complex Hilbert space. Its Calkin
algebra is the quotient `B(H)/K(H)` of bounded operators by compact operators, with the quotient
C*-norm. The star-algebra class map evaluates at every bounded operator `T` to the same quotient
class as the continuous algebra class map. -/
theorem classStarMap_apply_eq_classMap (T : H →L[ℂ] H) :
    classStarMap (H := H) T = classMap (𝕜 := ℂ) (E := H) T :=
  rfl

/-- **Equality of the Calkin class-map functions.** Let `H` be a complete complex Hilbert space. Its
Calkin algebra is the quotient `B(H)/K(H)` of bounded operators by compact operators, with the
quotient C*-norm. The functions underlying the star-algebra class map and the continuous algebra
class map from `B(H)` to the Calkin algebra agree. -/
theorem coe_classStarMap_eq_classMap :
    (classStarMap (H := H) : (H →L[ℂ] H) → CalkinAlgebra ℂ H) =
      classMap (𝕜 := ℂ) (E := H) :=
  rfl

/-- **Continuity of the Calkin star projection.** Let `H` be a complete complex Hilbert space. Its
Calkin algebra is the quotient `B(H)/K(H)` of bounded operators by compact operators, with the
quotient C*-norm. The star-algebra quotient projection from `B(H)` to its Calkin algebra is
norm-continuous. -/
theorem classStarMap_continuous : Continuous (classStarMap (H := H)) :=
  (classMap (𝕜 := ℂ) (E := H)).continuous

/-- **Surjectivity of the Calkin star projection.** Let `H` be a complete complex Hilbert space. Its
Calkin algebra is the quotient `B(H)/K(H)` of bounded operators by compact operators, with the
quotient C*-norm. Every Calkin element is the class of a bounded operator on `H`. -/
theorem classStarMap_surjective :
    Function.Surjective (classStarMap (H := H)) :=
  classMap_surjective

/-- **Zero class characterizes compactness.** Let `H` be a complete complex Hilbert space. Its Calkin
algebra is the quotient `B(H)/K(H)` of bounded operators by compact operators, with the quotient
C*-norm. A bounded operator has zero Calkin class exactly when it is compact. -/
@[simp]
theorem classStarMap_eq_zero_iff (T : H →L[ℂ] H) :
    classStarMap (H := H) T = 0 ↔ IsCompactOperator T :=
  classMap_eq_zero_iff T

/-- **The Calkin star map preserves adjoints.** Let `H` be a complete complex Hilbert space. Its Calkin
algebra is the quotient `B(H)/K(H)` of bounded operators by compact operators, with the quotient
C*-norm. For every bounded operator `T`, the star class map sends `T*` to `[T]*`. -/
@[simp]
theorem classStarMap_star (T : H →L[ℂ] H) :
    classStarMap (H := H) (star T) = star (classStarMap (H := H) T) :=
  map_star (classStarMap (H := H)) T

end CalkinAlgebra
