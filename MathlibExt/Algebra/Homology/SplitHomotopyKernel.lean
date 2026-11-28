/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.HomologicalComplex.SplitExact
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# The actual kernel contraction of a split homotopy equivalence

The kernel retraction is the native lift of identity minus the split
projection. Restricting the given homotopy and postcomposing with this
retraction constructs a contraction of the actual categorical kernel.
Kernel acyclicity is a conclusion, never a certificate supplied by a caller.
-/

@[expose] public section
noncomputable section

open CategoryTheory Limits

universe u v

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type*} {c : ComplexShape ι} [DecidableRel c.Rel]
  {K L : HomologicalComplex C c}
  (f : K ⟶ L) (g : L ⟶ K) (hg : g ≫ f = 𝟙 L)

/-- The actual split-complement projection lifts to the native kernel. -/
def splitHomotopyKernelRetraction : K ⟶ kernel f :=
  kernel.lift f (𝟙 K - f ≫ g) (by
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, hg,
      Category.comp_id, sub_self])

omit [DecidableRel c.Rel] in
/-- Its ambient value is exactly the original split-complement projection. -/
@[reassoc]
theorem splitHomotopyKernelRetraction_ι :
    splitHomotopyKernelRetraction f g hg ≫ kernel.ι f = 𝟙 K - f ≫ g :=
  kernel.lift_ι _ _ _

omit [DecidableRel c.Rel] in
/-- The native kernel inclusion followed by the constructed retraction is identity. -/
@[reassoc]
theorem kernel_ι_splitHomotopyKernelRetraction :
    kernel.ι f ≫ splitHomotopyKernelRetraction f g hg = 𝟙 (kernel f) := by
  apply (cancel_mono (kernel.ι f)).1
  rw [Category.assoc, splitHomotopyKernelRetraction_ι, Category.id_comp,
    Preadditive.comp_sub, Category.comp_id, ← Category.assoc, kernel.condition,
    Limits.zero_comp, sub_zero]

/-- Restricting and projecting the actual ambient homotopy contracts the actual kernel. -/
def splitHomotopyKernelContraction (h : Homotopy (f ≫ g) (𝟙 K)) :
    Homotopy (𝟙 (kernel f)) 0 := by
  let r := splitHomotopyKernelRetraction f g hg
  have hrestricted : Homotopy ((kernel.ι f ≫ 𝟙 K) ≫ r)
      ((kernel.ι f ≫ (f ≫ g)) ≫ r) :=
    (h.symm.compLeft (kernel.ι f)).compRight r
  have hleft : (kernel.ι f ≫ 𝟙 K) ≫ r = 𝟙 (kernel f) := by
    rw [Category.comp_id]
    exact kernel_ι_splitHomotopyKernelRetraction f g hg
  have hright : (kernel.ι f ≫ (f ≫ g)) ≫ r = 0 := by
    rw [← Category.assoc, kernel.condition, Limits.zero_comp, Limits.zero_comp]
  exact (Homotopy.ofEq hleft.symm).trans (hrestricted.trans (Homotopy.ofEq hright))

omit [DecidableRel c.Rel] in
/-- The constructed kernel contraction makes that kernel contractible. -/
theorem splitHomotopyKernel_contractible (hg : g ≫ f = 𝟙 L)
    (h : Homotopy (f ≫ g) (𝟙 K)) : Nonempty (Homotopy (𝟙 (kernel f)) 0) := by
  classical
  exact ⟨splitHomotopyKernelContraction f g hg h⟩

omit [DecidableRel c.Rel] in
/-- Every homology degree of the actual kernel vanishes, by the actual constructed contraction. -/
theorem splitHomotopyKernel_acyclic (hg : g ≫ f = 𝟙 L)
    (h : Homotopy (f ≫ g) (𝟙 K)) : (kernel f).Acyclic := by
  classical
  exact acyclic_of_homotopy_id_zero (splitHomotopyKernel_contractible f g hg h).some

end HomologicalComplex
