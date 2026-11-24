/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
public import Mathlib.Algebra.Homology.Embedding.Splitting
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit

/-!
# Contractible quotients in degreewise split sequences

For a degreewise split sequence of nonnegative chain complexes, a
contractible quotient gives the corresponding homotopy-equivalence
criterion for its first map. Extension through `n ↦ -n` transports the
splittings to integer cochains, where the comparison uses evaluation
isomorphisms and zero objects. No abelian category or square-zero condition
on the contracting homotopy is required.
-/

@[expose] public section
noncomputable section

open CategoryTheory Category Limits HomologicalComplex

universe u v

namespace ChainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]
  (S : ShortComplex (ChainComplex C ℕ))
  (σ : ∀ n, (S.map (eval C (ComplexShape.down ℕ) n)).Splitting)
  (h : Homotopy (𝟙 S.X₃) 0)

include σ h

/-- A contractible quotient makes the actual first map a homotopy equivalence. -/
theorem homotopyEquivalences_f_of_degreewiseSplit :
    homotopyEquivalences C (ComplexShape.down ℕ) S.f := by
  let e := ComplexShape.embeddingDownNat
  let S' := S.map (e.extendFunctor C)
  have h' : Homotopy (𝟙 S'.X₃) 0 := by
    change Homotopy (𝟙 (S.X₃.extend e)) 0
    simpa only [extendMap_id, extendMap_zero] using h.extend e
  have hf := (CochainComplex.homotopyEquivalences_shortComplexF_iff_of_splitting S'
    (e.splittingExtend σ)).2 ⟨h'⟩
  exact (homotopyEquivalences_extendMap_iff S.f e).1 hf

/-- A native homotopy-equivalence witness whose forward map is the original first map. -/
def homotopyEquivOfDegreewiseSplit : HomotopyEquiv S.X₁ S.X₂ :=
  Classical.choose (homotopyEquivalences_f_of_degreewiseSplit S σ h)

/-- Extracting the witness preserves the actual original map. -/
@[simp]
theorem homotopyEquivOfDegreewiseSplit_hom :
    (homotopyEquivOfDegreewiseSplit S σ h).hom = S.f :=
  Classical.choose_spec (homotopyEquivalences_f_of_degreewiseSplit S σ h)

end ChainComplex
