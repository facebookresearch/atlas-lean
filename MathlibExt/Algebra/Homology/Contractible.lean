/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# Contractible homological complexes

A homological complex is contractible when its identity map is chain
homotopic to zero.  Homotopic maps induce the same map on homology, so a
specified contraction forces every homology object to vanish and therefore
makes the complex acyclic.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {ι : Type*} {c : ComplexShape ι}

/-- A homological complex is contractible when its identity is homotopic to
zero. -/
def Contractible (K : HomologicalComplex C c) : Prop :=
  Nonempty (Homotopy (𝟙 K) 0)

/-- A specified contraction makes a complex acyclic. -/
theorem acyclic_of_id_homotopic_zero {K : HomologicalComplex C c}
    (h : Homotopy (𝟙 K) 0) [∀ i, K.HasHomology i] :
    K.Acyclic := by
  rw [acyclic_iff]
  intro i
  rw [exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero]
  simpa using h.homologyMap_eq i

/-- Every contractible complex is acyclic. -/
theorem Contractible.acyclic {K : HomologicalComplex C c}
    (h : K.Contractible) [∀ i, K.HasHomology i] :
    K.Acyclic :=
  acyclic_of_id_homotopic_zero h.some

end HomologicalComplex
