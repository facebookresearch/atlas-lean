/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.Index

/-!
# Fixing subgroups of a tower of intermediate fields

Let `E/F` be a field extension and `K ≤ L` intermediate fields, with fixing subgroups
`G_K = Gal(E/K)` and `G_L = Gal(E/L)` in `Gal(E/F)` (`IntermediateField.fixingSubgroup`), so that
`G_L ≤ G_K` (`IntermediateField.fixingSubgroup_le`). Suppose that `L/K` is normal, where `L` is
viewed as an intermediate field of `E/K` (`IntermediateField.extendScalars`). Then restriction to
`L` is a homomorphism `G_K → Gal(L/K)` (`IntermediateField.fixingSubgroupRestrict`) with kernel
`G_L` (`IntermediateField.ker_fixingSubgroupRestrict`). Hence

* `G_L` is a normal subgroup of `G_K` (`IntermediateField.normal_subgroupOf_fixingSubgroup`);
* if `L/K` is finite, `G_L` has finite index in `G_K`
  (`IntermediateField.finiteIndex_subgroupOf_fixingSubgroup`);
* if moreover `E/K` is normal, restriction is onto, and `G_K/G_L ≃ Gal(L/K)`
  (`IntermediateField.quotientFixingSubgroupEquiv`).

For an intermediate field `M` with `K ≤ M`, `M/K` is normal if `M/F` is
(`IntermediateField.normal_extendScalars`), and finite if `M/F` is
(`IntermediateField.finiteDimensional_extendScalars`); then `K/F` is finite too
(`IntermediateField.finiteDimensional_of_le`).

For `E/F` finite Galois these are parts of the fundamental theorem of Galois theory; here `E/F` is
arbitrary, for instance an algebraic closure.
-/

@[expose] public noncomputable section

namespace IntermediateField

variable {F E : Type*} [Field F] [Field E] [Algebra F E] {K L : IntermediateField F E}

/-- **Restriction to `L` of the automorphisms of `E` fixing `K`**, for `K ≤ L` with `L/K` normal:
the homomorphism `Gal(E/K) → Gal(L/K)`, `σ ↦ σ|_L`, on the fixing subgroup of `K` in `Gal(E/F)`,
where `L` is viewed as an intermediate field of `E/K`. -/
def fixingSubgroupRestrict (h : K ≤ L) [Normal K (extendScalars h)] :
    K.fixingSubgroup →* Gal(extendScalars h / K) :=
  (AlgEquiv.restrictNormalHom (extendScalars h)).comp K.fixingSubgroupEquiv.toMonoidHom

/-- `fixingSubgroupRestrict h σ` is the restriction of `σ` to `L`. -/
@[simp]
theorem coe_fixingSubgroupRestrict_apply (h : K ≤ L) [Normal K (extendScalars h)]
    (σ : K.fixingSubgroup) (x : extendScalars h) :
    (fixingSubgroupRestrict h σ x : E) = (σ : Gal(E/F)) x :=
  AlgEquiv.restrictNormal_commutes (K.fixingSubgroupEquiv σ) (extendScalars h) x

/-- **The kernel of the restriction `Gal(E/K) → Gal(L/K)` is `Gal(E/L)`**, for `K ≤ L` with
`L/K` normal: an automorphism of `E` fixing `K` restricts to the identity of `L` if and only if it
fixes `L`. -/
theorem ker_fixingSubgroupRestrict (h : K ≤ L) [Normal K (extendScalars h)] :
    (fixingSubgroupRestrict h).ker = L.fixingSubgroup.subgroupOf K.fixingSubgroup := by
  ext σ
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_fixingSubgroup_iff]
  constructor
  · intro hσ x hx
    have := coe_fixingSubgroupRestrict_apply h σ ⟨x, (mem_extendScalars h).2 hx⟩
    rw [hσ] at this
    exact this.symm
  · intro hσ
    refine AlgEquiv.ext fun x => Subtype.ext ?_
    rw [coe_fixingSubgroupRestrict_apply, AlgEquiv.one_apply]
    exact hσ x ((mem_extendScalars h).1 x.2)

/-- **`Gal(E/L)` is a normal subgroup of `Gal(E/K)`**, for `K ≤ L` with `L/K` normal. -/
theorem normal_subgroupOf_fixingSubgroup (h : K ≤ L) [Normal K (extendScalars h)] :
    (L.fixingSubgroup.subgroupOf K.fixingSubgroup).Normal := by
  rw [← ker_fixingSubgroupRestrict h]
  exact MonoidHom.normal_ker _

/-- **`Gal(E/L)` has finite index in `Gal(E/K)`**, for `K ≤ L` with `L/K` finite and normal. -/
theorem finiteIndex_subgroupOf_fixingSubgroup (h : K ≤ L) [Normal K (extendScalars h)]
    [FiniteDimensional K (extendScalars h)] :
    (L.fixingSubgroup.subgroupOf K.fixingSubgroup).FiniteIndex := by
  rw [← ker_fixingSubgroupRestrict h]
  exact Subgroup.finiteIndex_ker _

/-- **The restriction `Gal(E/K) → Gal(L/K)` is onto**, for `K ≤ L` with `L/K` and `E/K`
normal. -/
theorem fixingSubgroupRestrict_surjective (h : K ≤ L) [Normal K (extendScalars h)] [Normal K E] :
    Function.Surjective (fixingSubgroupRestrict h) :=
  (AlgEquiv.restrictNormalHom_surjective E).comp K.fixingSubgroupEquiv.surjective

/-- **`Gal(E/K)/Gal(E/L) ≃ Gal(L/K)`**, for `K ≤ L` with `L/K` and `E/K` normal: the isomorphism
induced by the restriction `σ ↦ σ|_L`. -/
def quotientFixingSubgroupEquiv (h : K ≤ L) [Normal K (extendScalars h)] [Normal K E] :
    letI := normal_subgroupOf_fixingSubgroup h
    K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup ≃* Gal(extendScalars h / K) :=
  letI := normal_subgroupOf_fixingSubgroup h
  (QuotientGroup.quotientMulEquivOfEq (ker_fixingSubgroupRestrict h).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (fixingSubgroupRestrict_surjective h))

/-- `quotientFixingSubgroupEquiv h` maps the class of `σ` to the restriction of `σ` to `L`. -/
@[simp]
theorem quotientFixingSubgroupEquiv_mk (h : K ≤ L) [Normal K (extendScalars h)] [Normal K E]
    (σ : K.fixingSubgroup) :
    letI := normal_subgroupOf_fixingSubgroup h
    quotientFixingSubgroupEquiv h σ = fixingSubgroupRestrict h σ :=
  rfl

/-! ### Intermediate fields of a finite or normal extension -/

section Tower

variable {M : IntermediateField F E}

/-- **A normal extension is normal over every intermediate field**: if `M/F` is normal, then
`M/K` is normal for every intermediate field `K ≤ M`. -/
theorem normal_extendScalars (h : K ≤ M) [Normal F M] : Normal K (extendScalars h) :=
  have : Normal F (extendScalars h) := inferInstanceAs (Normal F M)
  Normal.tower_top_of_normal F K (extendScalars h)

/-- If `M/F` is finite, then `M/K` is finite for every intermediate field `K ≤ M`. -/
theorem finiteDimensional_extendScalars (h : K ≤ M) [FiniteDimensional F M] :
    FiniteDimensional K (extendScalars h) :=
  have : FiniteDimensional F (extendScalars h) := inferInstanceAs (FiniteDimensional F M)
  FiniteDimensional.right F K (extendScalars h)

/-- If `M/F` is finite, then `K/F` is finite for every intermediate field `K ≤ M`. -/
theorem finiteDimensional_of_le (h : K ≤ M) [FiniteDimensional F M] : FiniteDimensional F K :=
  have : FiniteDimensional F (extendScalars h) := inferInstanceAs (FiniteDimensional F M)
  FiniteDimensional.left F K (extendScalars h)

end Tower

end IntermediateField
