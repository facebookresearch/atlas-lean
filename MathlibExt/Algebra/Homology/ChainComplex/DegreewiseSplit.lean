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
# Homotopy equivalences from degreewise split sequences

Let C be preadditive with a zero object and binary biproducts, and let S : X₁ → X₂ → X₃ be a
short complex of nonnegative chain complexes split in every degree. If X₃ is contractible, its
first map S.f : X₁ → X₂ is a homotopy equivalence. The chosen equivalence has forward map
exactly S.f; no abelian-category assumption or square-zero condition on the contracting homotopy
is required.
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

/-- Let C be preadditive with a zero object and binary biproducts. Let S : X₁ → X₂ → X₃ be a short
complex of natural-number-indexed chain complexes, choose a splitting of S in every degree, and
let h be a contracting homotopy of X₃, so id_X₃ is homotopic to zero. Then the first chain map
S.f : X₁ → X₂ is a homotopy equivalence. -/
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

/-- Let C be preadditive with a zero object and binary biproducts. Let S : X₁ → X₂ → X₃ be a short
complex of natural-number-indexed chain complexes, choose a splitting of S in every degree, and
let h be a contracting homotopy of X₃, so id_X₃ is homotopic to zero. The resulting homotopy
equivalence X₁ ≃ₕ X₂ has forward chain map S.f. -/
def homotopyEquivOfDegreewiseSplit : HomotopyEquiv S.X₁ S.X₂ :=
  Classical.choose (homotopyEquivalences_f_of_degreewiseSplit S σ h)

/-- Let C be preadditive with a zero object and binary biproducts. Let S : X₁ → X₂ → X₃ be a short
complex of natural-number-indexed chain complexes, choose a splitting of S in every degree, and
let h be a contracting homotopy of X₃, so id_X₃ is homotopic to zero. The forward map of
homotopyEquivOfDegreewiseSplit S is exactly the first map S.f. -/
@[simp]
theorem homotopyEquivOfDegreewiseSplit_hom :
    (homotopyEquivOfDegreewiseSplit S σ h).hom = S.f :=
  Classical.choose_spec (homotopyEquivalences_f_of_degreewiseSplit S σ h)

end ChainComplex
