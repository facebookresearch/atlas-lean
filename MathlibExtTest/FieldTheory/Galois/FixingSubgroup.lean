/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.FieldTheory.Galois.FixingSubgroup
import Mathlib.FieldTheory.Normal.Closure

/-! Tests for the fixing subgroups of a tower `K ≤ L` of intermediate fields with `L/K` normal:
`Gal(E/L)` is normal and of finite index in `Gal(E/K)`, with quotient `Gal(L/K)` when `E/K` is
normal, for instance for an algebraic closure; and normal closures give normal extensions of
every intermediate field. -/

open IntermediateField

variable {F E : Type*} [Field F] [Field E] [Algebra F E] {K L : IntermediateField F E}

-- `Gal(E/L)` is normal and of finite index in `Gal(E/K)` for `L/K` finite and normal.
example (h : K ≤ L) [Normal K (extendScalars h)] [FiniteDimensional K (extendScalars h)] :
    (L.fixingSubgroup.subgroupOf K.fixingSubgroup).Normal ∧
      (L.fixingSubgroup.subgroupOf K.fixingSubgroup).FiniteIndex :=
  ⟨normal_subgroupOf_fixingSubgroup h, finiteIndex_subgroupOf_fixingSubgroup h⟩

-- The kernel of the restriction is `Gal(E/L)`, and restriction acts on `L` as the automorphism.
example (h : K ≤ L) [Normal K (extendScalars h)] (σ : K.fixingSubgroup) (x : extendScalars h) :
    (fixingSubgroupRestrict h).ker = L.fixingSubgroup.subgroupOf K.fixingSubgroup ∧
      (fixingSubgroupRestrict h σ x : E) = (σ : Gal(E/F)) x :=
  ⟨ker_fixingSubgroupRestrict h, coe_fixingSubgroupRestrict_apply h σ x⟩

-- For an algebraic closure, `Gal(E/K)/Gal(E/L) ≃ Gal(L/K)`.
noncomputable example {K L : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : K ≤ L)
    [Normal K (extendScalars h)] :
    letI := normal_subgroupOf_fixingSubgroup h
    K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup ≃* Gal(extendScalars h / K) :=
  quotientFixingSubgroupEquiv h

-- The normal closure `M` of a finite intermediate field `L` of a normal extension `E/F` is finite
-- and normal over every intermediate field `K ≤ M`, in particular over `L`.
example [Normal F E] (L : IntermediateField F E) [FiniteDimensional F L] :
    let M := normalClosure F L E
    have h : L ≤ M := le_normalClosure L
    Normal L (extendScalars h) ∧ FiniteDimensional L (extendScalars h) :=
  ⟨normal_extendScalars _, finiteDimensional_extendScalars _⟩
