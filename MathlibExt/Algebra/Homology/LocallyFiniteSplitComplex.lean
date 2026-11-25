/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import MathlibExt.CategoryTheory.Linear.LocallyFiniteSplitCoproduct

/-!
# Actual locally finite split-complex coproduct inverses

The original chain-map inclusions define the native complex coproduct
descent. In every original degree, the actual finite sum of image
projections and coproduct inclusions gives its inverse. Native evaluation
preserves the coproduct, so its original legs are jointly detecting.
The actual split/cross/projector/support laws prove component invertibility;
native homological-complex isomorphism detection gives the complex
isomorphism. No global AB5, homology preservation or supplied isomorphism
certificate is assumed.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

universe u v w

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasColimitsOfShape (Discrete ℕ) C]
  {ι : Type w} {c : ComplexShape ι}
  (K : HomologicalComplex C c) (F : ℕ → HomologicalComplex C c)
  (i : ∀ j : ℕ, F j ⟶ K) (p : ∀ j : ℕ, K ⟶ F j)
  (hsplit : ∀ j : ℕ, i j ≫ p j = 𝟙 (F j))
  (hcross : ∀ j k : ℕ, j ≠ k → i j ≫ p k = 0)
  (N : ι → ℕ)
  (hsupport : ∀ n : ι, ∀ j : ℕ, N n < j → (p j).f n = 0)
  (hsum : ∀ n : ι, (∑ j : Fin (N n + 1), (p j).f n ≫ (i j).f n) = 𝟙 (K.X n))

/-- The original native sum of the actual image-complex inclusions. -/
def splitComplexCoproductMap : (∐ F) ⟶ K := Sigma.desc i

/-- The actual finite projection formula in each original complex degree. -/
def splitComplexCoproductInverseAt (n : ι) : K.X n ⟶ (∐ F).X n :=
  ∑ j : Fin (N n + 1), (p j.val).f n ≫ (Sigma.ι F j.val).f n

/-- The actual original coproduct chain legs retain the actual original component inclusions. -/
@[reassoc]
theorem splitComplexCoproduct_leg (j : ℕ) (n : ι) :
    (Sigma.ι F j).f n ≫ (splitComplexCoproductMap K F i).f n = (i j).f n := by
  exact congrArg (fun f => f.f n) (Sigma.ι_comp_desc i j)

include hsum in
/-- The actual finite projector sum is the right component inverse. -/
@[reassoc]
theorem splitComplexCoproductInverseAt_map (n : ι) :
    splitComplexCoproductInverseAt K F p N n ≫ (splitComplexCoproductMap K F i).f n = 𝟙 (K.X n) := by
  rw [splitComplexCoproductInverseAt, Preadditive.sum_comp]
  simp only [Category.assoc, splitComplexCoproduct_leg]
  exact hsum n

include hsplit hcross hsupport in
/-- Native evaluation of the actual coproduct proves the left component inverse from original split and cross maps. -/
@[reassoc]
theorem splitComplexCoproductMap_inverseAt (n : ι) :
    (splitComplexCoproductMap K F i).f n ≫ splitComplexCoproductInverseAt K F p N n =
      𝟙 ((∐ F).X n) := by
  let E := HomologicalComplex.eval C c n
  have hc : IsColimit (E.mapCocone (colimit.cocone (Discrete.functor F))) :=
    isColimitOfPreserves E (colimit.isColimit (Discrete.functor F))
  apply hc.hom_ext
  rintro ⟨j⟩
  change (Sigma.ι F j).f n ≫ ((splitComplexCoproductMap K F i).f n ≫
      splitComplexCoproductInverseAt K F p N n) = (Sigma.ι F j).f n ≫ 𝟙 _
  rw [← Category.assoc, splitComplexCoproduct_leg, splitComplexCoproductInverseAt,
    Preadditive.comp_sum, Category.comp_id]
  by_cases hj : j ≤ N n
  · let j₀ : Fin (N n + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
    rw [Finset.sum_eq_single j₀]
    · have h := congrArg (fun f => f.f n) (hsplit j)
      simpa only [j₀, Category.assoc, HomologicalComplex.comp_f,
        HomologicalComplex.id_f, Category.id_comp] using
        congrArg (fun f => f ≫ (Sigma.ι F j).f n) h
    · intro k hk hne
      have hjk : j ≠ k.val := fun h => hne (Fin.ext h.symm)
      have h := congrArg (fun f => f.f n) (hcross j k.val hjk)
      rw [← Category.assoc, ← HomologicalComplex.comp_f, h, HomologicalComplex.zero_f, zero_comp]
    · simp
  · have hj' : N n < j := Nat.lt_of_not_ge hj
    have hid : 𝟙 ((F j).X n) = 0 := by
      have h := congrArg (fun f => f.f n) (hsplit j)
      rw [HomologicalComplex.comp_f, hsupport n j hj', comp_zero, HomologicalComplex.id_f] at h
      exact h.symm
    have hleg : (Sigma.ι F j).f n = 0 := by
      rw [← Category.id_comp ((Sigma.ι F j).f n), hid, zero_comp]
    rw [hleg]
    apply Finset.sum_eq_zero
    intro k hk
    have hjk : j ≠ k.val := by have hkn := k.isLt; omega
    have h := congrArg (fun f => f.f n) (hcross j k.val hjk)
    rw [← Category.assoc, ← HomologicalComplex.comp_f, h, HomologicalComplex.zero_f, zero_comp]

include hsplit hcross hsupport hsum in
/-- Each original coproduct-map component is actually invertible with its original finite projection inverse. -/
theorem isIso_splitComplexCoproductMap_f (n : ι) :
    IsIso ((splitComplexCoproductMap K F i).f n) := by
  let e : (∐ F).X n ≅ K.X n :=
    { hom := (splitComplexCoproductMap K F i).f n
      inv := splitComplexCoproductInverseAt K F p N n
      hom_inv_id := splitComplexCoproductMap_inverseAt K F i p hsplit hcross N hsupport n
      inv_hom_id := splitComplexCoproductInverseAt_map K F i p N hsum n }
  exact e.isIso_hom

include hsplit hcross hsupport hsum in
/-- Native componentwise detection gives the original locally finite complex coproduct isomorphism. -/
def locallyFiniteSplitComplexCoproductIso : (∐ F) ≅ K := by
  letI : ∀ n : ι, IsIso ((splitComplexCoproductMap K F i).f n) :=
    fun n => isIso_splitComplexCoproductMap_f K F i p hsplit hcross N hsupport hsum n
  letI := HomologicalComplex.Hom.isIso_of_components (splitComplexCoproductMap K F i)
  exact asIso (splitComplexCoproductMap K F i)

end HomologicalComplex
