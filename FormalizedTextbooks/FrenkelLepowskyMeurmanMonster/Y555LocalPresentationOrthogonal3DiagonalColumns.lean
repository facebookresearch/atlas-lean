/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact norm and support conditions for actual diagonal-isometry orbit columns. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3DiagonalChain

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- The columns of any actual diagonal isometry have exactly their prescribed weighted pairings. -/
theorem y322Orthogonal3DiagonalGroup_columns
    (g : Matrix.GeneralLinearGroup (Fin 7) (ZMod 3))
    (hg : g ∈ y322Orthogonal3DiagonalGroup) (i j : Fin 7) :
    (∑ k : Fin 7, y322Orthogonal3DiagonalWeight k * g.val k i * g.val k j) =
      if i = j then y322Orthogonal3DiagonalWeight i else 0 := by
  change g.val.transpose * y322Orthogonal3DiagonalGram * g.val =
    y322Orthogonal3DiagonalGram at hg
  have h := congrArg (fun m : Matrix (Fin 7) (Fin 7) (ZMod 3) => m i j) hg
  rw [mul_assoc] at h
  change (∑ k : Fin 7, g.val k i *
    (y322Orthogonal3DiagonalGram * g.val) k j) = y322Orthogonal3DiagonalGram i j at h
  simpa only [y322Orthogonal3DiagonalGram, Matrix.diagonal_mul, Matrix.diagonal_apply,
    mul_left_comm, mul_comm, mul_assoc] using h

/-- Later fixed columns force the free orbit column to have zero later coordinates. -/
theorem y322Orthogonal3DiagonalChain_column_zero (i j : Fin 7)
    (g : y322Orthogonal3DiagonalChain (i.val + 1)) (hij : i.val < j.val) :
    g.val.val j i = 0 := by
  obtain ⟨hform, hfix⟩ := (y322Orthogonal3DiagonalChain_mem _ g.val).mp g.property
  have hj := hfix j (by omega)
  have hcol : ∀ k : Fin 7, g.val.val k j = if k = j then 1 else 0 := by
    intro k
    have h := congrArg (fun v : Matrix (Fin 7) Unit (ZMod 3) => v k ()) hj
    rw [y322Orthogonal3DiagonalUnit_action] at h
    exact h
  have hpair := y322Orthogonal3DiagonalGroup_columns g.val hform j i
  have hne : j ≠ i := by intro h; subst j; omega
  simp only [hcol, hne, ite_false, mul_ite, mul_one, mul_zero, ite_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hpair
  exact (mul_eq_zero.mp hpair).resolve_left (y322Orthogonal3DiagonalWeight_ne_zero j)

/-- Each actual orbit column has the exact finite candidate support and norm. -/
theorem y322Orthogonal3DiagonalChain_column_candidate (i : Fin 7)
    (g : y322Orthogonal3DiagonalChain (i.val + 1)) :
    y322Orthogonal3DiagonalCandidateProperty i (fun r => g.val.val r i) := by
  refine ⟨fun j hj => y322Orthogonal3DiagonalChain_column_zero i j g hj, ?_⟩
  obtain ⟨hform, _⟩ := (y322Orthogonal3DiagonalChain_mem _ g.val).mp g.property
  simpa only [y322Orthogonal3DiagonalNorm, ite_true] using
    y322Orthogonal3DiagonalGroup_columns g.val hform i i

/-- Reading a single-column orbit gives an injection into the exact independent candidate type. -/
def y322Orthogonal3DiagonalChainOrbitCandidate (i : Fin 7)
    (v : MulAction.orbit (y322Orthogonal3DiagonalChain (i.val + 1))
      (y322Orthogonal3DiagonalUnit i)) : Y322Orthogonal3DiagonalCandidate i :=
  ⟨fun r => v.val r (), by
    obtain ⟨g, hg⟩ := v.property
    have h := y322Orthogonal3DiagonalChain_column_candidate i g
    convert h using 1
    ext r
    have heq := congrArg (fun m : Matrix (Fin 7) Unit (ZMod 3) => m r ()) hg
    simpa only [Subgroup.smul_def, y322Orthogonal3DiagonalUnit_action] using heq.symm⟩

/-- The orbit candidate map preserves every coordinate and is therefore injective. -/
theorem y322Orthogonal3DiagonalChainOrbitCandidate_injective (i : Fin 7) :
    Function.Injective (y322Orthogonal3DiagonalChainOrbitCandidate i) := by
  intro v w h
  apply Subtype.ext
  ext r u
  cases u
  exact congrFun (congrArg Subtype.val h) r

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
