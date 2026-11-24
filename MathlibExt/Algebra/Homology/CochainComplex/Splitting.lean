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
# Literal integer-cochain inverse families

The source family sends degree n+1 to degree n and satisfies d = d s d. Its bundled splitting is
obtained from the existing integer-chain constructor on the opposite complex, followed by the
existing unop operation. The raw construction uses only zero morphisms. Signed transport
separately uses the preadditive integer shift.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CochainComplex

universe u v

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- A literal degree-minus-one family supplies the existing generic splitting through op/unop. -/
def splittingOfDegreeMinusOneHom (K : CochainComplex C ℤ)
    (s : ∀ n : ℤ, K.X (n + 1) ⟶ K.X n)
    (hs : ∀ n : ℤ, K.d n (n + 1) = K.d n (n + 1) ≫ s n ≫ K.d n (n + 1)) :
    Splitting K :=
  (ChainComplex.splittingOfDegreeOneHom K.op (fun n => (s n).op) (fun n => by
    apply Quiver.Hom.unop_inj
    simpa only [HomologicalComplex.op_d, unop_comp, Quiver.Hom.unop_op,
      Category.assoc] using hs n)).unop

/-- The adjacent bundled cochain inverse is exactly the original source family. -/
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
  change ((ChainComplex.splittingOfDegreeOneHom K' (fun n => (s n).op) hs').hom n (n + 1)).unop = s n
  exact congrArg Quiver.Hom.unop (ChainComplex.splittingOfDegreeOneHom_hom_succ K' (fun n => (s n).op) hs' n)

/-- Integer cochain splitness is the literal degree-minus-one generalized-inverse condition. -/
lemma isSplit_iff_exists_degreeMinusOneHom (K : CochainComplex C ℤ) :
    IsSplit K ↔
      ∃ s : ∀ n : ℤ, K.X (n + 1) ⟶ K.X n,
        ∀ n : ℤ, K.d n (n + 1) = K.d n (n + 1) ≫ s n ≫ K.d n (n + 1) := by
  constructor
  · rintro ⟨s⟩
    exact ⟨fun n => s.hom (n + 1) n, fun n => (s.d_h_d n (n + 1)).symm⟩
  · rintro ⟨s, hs⟩
    exact ⟨splittingOfDegreeMinusOneHom K s hs⟩

/-- Extracting adjacent cochain components and rebuilding restores the full splitting. -/
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
