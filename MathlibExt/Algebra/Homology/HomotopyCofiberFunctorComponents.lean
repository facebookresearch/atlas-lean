/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Homology.HomotopyCofiber

/-!
# Additive functors and components of maps out of cofibers

Let H:C → D be an additive functor between preadditive categories with
binary biproducts, and let c be an arbitrary complex shape with decidable
differential relation. For φ:F → G there is a canonical comparison
ε:H(Cofib(φ)) ≅ Cofib(H(φ)).

For a cofiber map q:Cofib(φ) → K, set
q′=H(q) ∘ ε⁻¹:Cofib(H(φ)) → H(K).
Precomposing q′ with either the shifted-source inclusion or the target
inclusion gives H applied to the corresponding component of q.
The categories and shape index have independent universes.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uC vC uD vD w

namespace HomologicalComplex.homotopyCofiber

variable {C : Type uC} [Category.{vC} C] [Preadditive C] [HasBinaryBiproducts C]
  {D : Type uD} [Category.{vD} D] [Preadditive D] [HasBinaryBiproducts D]
  {ι : Type w} {c : ComplexShape ι} [DecidableRel c.Rel]
  (H : C ⥤ D) [H.Additive]
  {F G K : HomologicalComplex C c} (φ : F ⟶ G) (q : homotopyCofiber φ ⟶ K)

/-- Let H:C → D be additive, where C and D are preadditive with binary
biproducts, and let c have decidable differential relation.
For φ:F → G and q:Cofib(φ) → K, write
ε:H(Cofib(φ)) ≅ Cofib(H(φ)) and q′=H(q)∘ε⁻¹.
If c.Rel(j,i), the shifted-source inclusions satisfy
q′ⱼ ∘ inl_{Hφ}(i,j) = H(qⱼ ∘ inl_φ(i,j)). -/
@[reassoc]
theorem inlX_mapHomologicalComplexObjIso_inv_comp (i j : ι) (hji : c.Rel j i) :
    inlX ((H.mapHomologicalComplex c).map φ) i j hji ≫
      ((mapHomologicalComplexObjIso φ H).inv ≫ (H.mapHomologicalComplex c).map q).f j =
    H.map (inlX φ i j hji ≫ q.f j) := by
  change inlX ((H.mapHomologicalComplex c).map φ) i j hji ≫
      (mapHomologicalComplexObjXIso φ H j).inv ≫ H.map (q.f j) = _
  rw [inlX_mapHomologicalComplexObjXIso_inv_assoc, H.map_comp]

/-- Let H:C → D be additive between preadditive categories with binary
biproducts, and let c have decidable differential relation.
For φ:F → G and q:Cofib(φ) → K, put
q′=H(q)∘ε⁻¹ using ε:H(Cofib(φ)) ≅ Cofib(H(φ)).
The target components satisfy, in every degree i,
q′ᵢ ∘ inr_{Hφ}(i) = H(qᵢ ∘ inr_φ(i)). -/
@[reassoc]
theorem inrX_mapHomologicalComplexObjIso_inv_comp (i : ι) :
    inrX ((H.mapHomologicalComplex c).map φ) i ≫
      ((mapHomologicalComplexObjIso φ H).inv ≫ (H.mapHomologicalComplex c).map q).f i =
    H.map (inrX φ i ≫ q.f i) := by
  change inrX ((H.mapHomologicalComplex c).map φ) i ≫
      (mapHomologicalComplexObjXIso φ H i).inv ≫ H.map (q.f i) = _
  rw [inrX_mapHomologicalComplexObjXIso_inv_assoc, H.map_comp]

end HomologicalComplex.homotopyCofiber

end
