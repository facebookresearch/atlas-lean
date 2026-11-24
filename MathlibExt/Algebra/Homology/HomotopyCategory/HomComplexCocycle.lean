/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift

/-!
# Generic cocycle pre/post laws

Arbitrary preadditive-category, arbitrary-degree cocycle identity, composition, zero, and
interchange laws, plus shift-equivalence pre/post naturality, actually consumed by the
cohomology-class base actions and the forward twisting-representability map. Reuses
`Cocycle.precomp`/`postcomp` and `Cochain` laws; no larger functor abstraction.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CochainComplex.HomComplex.Cocycle

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {F G H K L : CochainComplex C ℤ} {n : ℤ}

/-- Precomposing a fixed-degree cocycle on the contravariant source side with the
identity leaves it unchanged; no shift or cohomology-level claim. -/
@[simp] theorem precomp_id (z : Cocycle G K n) : z.precomp (𝟙 G) = z := by
  apply Cocycle.ext
  simp

/-- Postcomposing a fixed-degree cocycle on the covariant target side with the
identity leaves it unchanged; no shift or cohomology-level claim. -/
@[simp] theorem postcomp_id (z : Cocycle F G n) : z.postcomp (𝟙 G) = z := by
  apply Cocycle.ext
  simp

/-- Source-side precomposition is contravariantly functorial at fixed degree,
turning precomposition with a composite into successive precompositions in reverse
order; no target-side or shift claim. -/
@[simp] theorem precomp_comp (z : Cocycle H K n) (f : F ⟶ G) (g : G ⟶ H) :
    z.precomp (f ≫ g) = (z.precomp g).precomp f := by
  apply Cocycle.ext
  simp

/-- Target-side postcomposition is covariantly functorial at fixed degree,
collapsing successive postcompositions to postcomposition with the composite;
no source-side or shift claim. -/
@[simp] theorem postcomp_comp (z : Cocycle F G n) (f : G ⟶ K) (g : K ⟶ L) :
    (z.postcomp f).postcomp g = z.postcomp (f ≫ g) := by
  apply Cocycle.ext
  simp

/-- Independent contravariant source precomposition and covariant target
postcomposition commute at fixed degree; no identity, zero, shift, or
cohomology-level claim. -/
theorem precomp_postcomp (z : Cocycle G K n) (f : K ⟶ L) (g : F ⟶ G) :
    (z.postcomp f).precomp g = (z.precomp g).postcomp f := by
  apply Cocycle.ext
  simp

/-- Precomposing a fixed-degree cocycle on the contravariant source side with the
zero map absorbs to the zero cocycle; source-zero absorption only, with no
target-side or shift claim. -/
@[simp] theorem precomp_zero (z : Cocycle G K n) :
    z.precomp (0 : F ⟶ G) = 0 := by
  apply Cocycle.ext
  simp

/-- Postcomposing a fixed-degree cocycle on the covariant target side with the
zero map absorbs to zero; target-zero absorption only, with no shift claim. -/
@[simp] theorem postcomp_zero (z : Cocycle F G n) :
    z.postcomp (0 : G ⟶ K) = 0 := by
  apply Cocycle.ext
  simp

/-- Postcomposing the zero cocycle itself on the covariant target side stays zero
at fixed degree; no claim about nonzero cocycles, shifts, or cohomology. -/
@[simp] theorem zero_postcomp (f : G ⟶ K) :
    (0 : Cocycle F G n).postcomp f = 0 := by
  apply Cocycle.ext
  simp

set_option backward.isDefEq.respectTransparency.types false in
/-- Contravariant source-side naturality of the shift equivalence at fixed shift
parameters: shifting `g` before the equivalence is cocycle precomposition after it,
under the degree condition `m + a = 0`. Fixed `a`/`m` only; no general
cohomology-level or unrestricted shift-functor claim. -/
theorem equivHomShift'_shift_comp {K' : CochainComplex C ℤ} {a m : ℤ} (h : m + a = 0)
    (g : K' ⟶ K) (f : K⟦a⟧ ⟶ L) :
    equivHomShift' a m h (g⟦a⟧' ≫ f) = Cocycle.precomp (equivHomShift' a m h f) g := by
  ext p q hpq
  have hqa : q + a = p := by omega
  subst hqa
  simp only [equivHomShift'_apply, Cocycle.leftUnshift_coe,
    Cochain.leftUnshift_v _ _ _ _ _ _ _ (add_zero q), precomp_coe,
    Cochain.zero_cochain_comp_v, Cocycle.ofHom_coe, Cochain.ofHom_v]
  erw [Category.id_comp]
  rw [Linear.comp_units_smul, ← Category.assoc]
  congr 1
  dsimp only [shiftFunctorObjXIso]
  simp only [Category.assoc]
  erw [Category.id_comp]
  rw [HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f']

set_option backward.isDefEq.respectTransparency.types false in
/-- Covariant target-side naturality of the shift equivalence at fixed shift
parameters: postcomposition before the equivalence is cocycle postcomposition after
it, under the degree condition `m + a = 0`. Fixed `a`/`m` only; no general
cohomology-level or unrestricted shift-functor claim. -/
theorem equivHomShift'_comp {L' : CochainComplex C ℤ} {a m : ℤ} (h : m + a = 0)
    (f : K⟦a⟧ ⟶ L) (g : L ⟶ L') :
    equivHomShift' a m h (f ≫ g) = Cocycle.postcomp (equivHomShift' a m h f) g := by
  ext p q hpq
  simp [equivHomShift'_apply, Cochain.leftUnshift_v _ _ _ _ _ _ _ (add_zero q)]

end CochainComplex.HomComplex.Cocycle
