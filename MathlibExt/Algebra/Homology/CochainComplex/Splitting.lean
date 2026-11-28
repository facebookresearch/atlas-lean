/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.HomologicalComplex.SplittingOpposite
public import MathlibExt.Algebra.Homology.HomologicalComplex.SplittingShift

/-!
# Generalized inverses for integer cochain differentials

A splitting of an integer cochain complex is equivalently a family
s_n : K^{n+1} → K^n with d_n s_n d_n = d_n at every integer degree.
These adjacent inverse maps determine the full reverse-shape splitting.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CochainComplex

universe u v

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-
The construction applies the chain splitting to the opposite complex and then takes unop.
-/

/--
Let K be an integer-indexed cochain complex in a category C with zero morphisms, with dₙ : Kⁿ
→ Kⁿ⁺¹. A family sₙ : Kⁿ⁺¹ → Kⁿ with dₙ = dₙ ≫ sₙ ≫ dₙ for every n ∈ ℤ defines a splitting of
K. Its adjacent component from Kⁿ⁺¹ to Kⁿ is sₙ, and components outside the reversed cochain
shape are zero.
-/
def splittingOfDegreeMinusOneHom (K : CochainComplex C ℤ)
    (s : ∀ n : ℤ, K.X (n + 1) ⟶ K.X n)
    (hs : ∀ n : ℤ, K.d n (n + 1) = K.d n (n + 1) ≫ s n ≫ K.d n (n + 1)) :
    Splitting K :=
  (ChainComplex.splittingOfDegreeOneHom K.op (fun n => (s n).op) (fun n => by
    apply Quiver.Hom.unop_inj
    simpa only [HomologicalComplex.op_d, unop_comp, Quiver.Hom.unop_op,
      Category.assoc] using hs n)).unop

/--
Let K be an integer-indexed cochain complex in a category C with zero morphisms, with dₙ : Kⁿ
→ Kⁿ⁺¹. For a family sₙ : Kⁿ⁺¹ → Kⁿ satisfying dₙ ≫ sₙ ≫ dₙ = dₙ at every degree, the
constructed splitting has component (splittingOfDegreeMinusOneHom K s hs).hom (n+1) n = sₙ.
-/
lemma splittingOfDegreeMinusOneHom_hom_succ (K : CochainComplex C ℤ)
    (s : ∀ n : ℤ, K.X (n + 1) ⟶ K.X n)
    (hs : ∀ n : ℤ, K.d n (n + 1) = K.d n (n + 1) ≫ s n ≫ K.d n (n + 1))
    (n : ℤ) :
    (splittingOfDegreeMinusOneHom K s hs).hom (n + 1) n = s n := by
  let K' : ChainComplex Cᵒᵖ ℤ := K.op
  have hs' : ∀ n : ℤ, K'.d (n + 1) n = K'.d (n + 1) n ≫ (s n).op ≫ K'.d (n + 1) n := by
    intro n
    apply Quiver.Hom.unop_inj
    simpa only [K', HomologicalComplex.op_d, unop_comp, Quiver.Hom.unop_op,
      Category.assoc] using hs n
  change ((ChainComplex.splittingOfDegreeOneHom K' (fun n => (s n).op) hs').hom n
    (n + 1)).unop = s n
  exact congrArg Quiver.Hom.unop
    (ChainComplex.splittingOfDegreeOneHom_hom_succ K' (fun n => (s n).op) hs' n)

/--
Let K be an integer-indexed cochain complex in a category C with zero morphisms, with dₙ : Kⁿ
→ Kⁿ⁺¹. The complex is split if and only if there exists a family sₙ : Kⁿ⁺¹ → Kⁿ such that dₙ
= dₙ ≫ sₙ ≫ dₙ for all n ∈ ℤ.
-/
lemma isSplit_iff_exists_degreeMinusOneHom (K : CochainComplex C ℤ) :
    IsSplit K ↔
      ∃ s : ∀ n : ℤ, K.X (n + 1) ⟶ K.X n,
        ∀ n : ℤ, K.d n (n + 1) = K.d n (n + 1) ≫ s n ≫ K.d n (n + 1) := by
  constructor
  · rintro ⟨s⟩
    exact ⟨fun n => s.hom (n + 1) n, fun n => (s.d_h_d n (n + 1)).symm⟩
  · rintro ⟨s, hs⟩
    exact ⟨splittingOfDegreeMinusOneHom K s hs⟩

/--
Let K be an integer-indexed cochain complex in a category C with zero morphisms, with dₙ : Kⁿ
→ Kⁿ⁺¹. If s is a splitting of K, its maps s.hom (n+1) n determine it completely. Constructing
the splitting from those adjacent maps and their generalized-inverse identities returns s.
-/
lemma splittingOfDegreeMinusOneHom_ofSplitting (K : CochainComplex C ℤ) (s : Splitting K) :
    splittingOfDegreeMinusOneHom K (fun n => s.hom (n + 1) n)
      (fun n => (s.d_h_d n (n + 1)).symm) = s := by
  ext i j
  by_cases hij : (ComplexShape.up ℤ).Rel j i
  · change j + 1 = i at hij
    subst i
    rw [splittingOfDegreeMinusOneHom_hom_succ]
  · rw [Splitting.zero _ i j hij, s.zero i j hij]

end CochainComplex
