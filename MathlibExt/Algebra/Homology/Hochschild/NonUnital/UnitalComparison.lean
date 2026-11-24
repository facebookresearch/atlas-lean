/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Basic

/-!
# The comparison with the unital Hochschild complex

The complexes have the same literal tensor objects. Their differentials agree
because the proved nonunital specialization has exactly the unital
face values. The native component-iso constructor supplies the chain
isomorphism; callers supply neither a comparison nor an object equality.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped BigOperators

universe u v w

namespace ModuleCat.Algebra.Hochschild.NonUnital

variable {k : Type u} [CommRing k] {A : Type v} [Ring A] [Algebra k A]
  {M : Type w} [AddCommGroup M] [Module k M]
  [Module A M] [Module Aᵐᵒᵖ M] [SMulCommClass A Aᵐᵒᵖ M]
  [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M]
  [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]

/-- Identity tensor components identify the unital and nonunital complexes. -/
def complexIsoUnital :
    let l := (Algebra.lsmul k k M (A := A)).toNonUnitalAlgHom
    let r := (Algebra.lsmul k k M (A := Aᵐᵒᵖ)).toNonUnitalAlgHom
    complex l r (fun a b m => smul_comm a b m) ≅
      ModuleCat.Algebra.Hochschild.chainComplex k A M := by
  let l : A →ₙₐ[k] Module.End k M :=
    (Algebra.lsmul k k M (A := A)).toNonUnitalAlgHom
  let r : Aᵐᵒᵖ →ₙₐ[k] Module.End k M :=
    (Algebra.lsmul k k M (A := Aᵐᵒᵖ)).toNonUnitalAlgHom
  have h : ∀ (a : A) (b : Aᵐᵒᵖ) (m : M), l a (r b m) = r b (l a m) := by
    intro a b m
    change a • (b • m) = b • (a • m)
    exact smul_comm a b m
  change complex l r h ≅ ModuleCat.Algebra.Hochschild.chainComplex k A M
  dsimp only [ModuleCat.Algebra.Hochschild.chainComplex, ChainComplex.of]
  exact HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j hij
    change j + 1 = i at hij
    subst i
    change 𝟙 (chainLevel k A M (j + 1)) ≫
        ChainComplex.of.d (chainLevel k A M)
          (ModuleCat.Algebra.Hochschild.boundary k A M) (j + 1) j =
      (complex l r h).d (j + 1) j ≫ 𝟙 (chainLevel k A M j)
    calc
      _ = ChainComplex.of.d (chainLevel k A M)
          (ModuleCat.Algebra.Hochschild.boundary k A M) (j + 1) j := Category.id_comp _
      _ = ModuleCat.Algebra.Hochschild.boundary k A M j := ChainComplex.of_d _ _ _
      _ = ∑ i : Fin (j + 2), (-1 : ℤ) ^ i.val •
          ModuleCat.Algebra.Hochschild.face k A M j i :=
        ModuleCat.Algebra.Hochschild.boundary_eq_sum k A M j
      _ = ∑ i : Fin (j + 2), (-1 : ℤ) ^ i.val • face l r h j i := by
        apply Finset.sum_congr rfl
        intro i _
        have hf : face l r h j i = ModuleCat.Algebra.Hochschild.face k A M j i := by
          exact face_eq_unital (k := k) (B := A) (M := M) j i
        exact congrArg (fun d : chainLevel k A M (j + 1) ⟶ chainLevel k A M j =>
          (-1 : ℤ) ^ i.val • d) hf.symm
      _ = (complex l r h).d (j + 1) j := (complex_d (l := l) (r := r) (h := h) j).symm
      _ = _ := (Category.comp_id ((complex l r h).d (j + 1) j)).symm)

@[simp]
theorem complexIsoUnital_hom_f (n : ℕ) :
    (complexIsoUnital (k := k) (A := A) (M := M)).hom.f n = 𝟙 _ := rfl

@[simp]
theorem complexIsoUnital_inv_f (n : ℕ) :
    (complexIsoUnital (k := k) (A := A) (M := M)).inv.f n = 𝟙 _ := rfl

end ModuleCat.Algebra.Hochschild.NonUnital
