/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteUnionWeakEquivalence
import MathlibExt.AlgebraicTopology.SimplicialSet.SubcomplexPreimageSortLimits
import Mathlib.AlgebraicTopology.SimplicialSet.Horn

/-!
# Whole original horn preimages from actual nonempty face comparisons

Every original maximal horn face and every complete finite intersection
is retained. Intersections are literally the faces on complementary
vertex sets; they all contain the original omitted horn vertex. Native
preimages preserve their full unions and intersections. The genuine
finite-union theorem therefore gives the actual whole horn-preimage
weak map, without a Kan or global weak-equivalence premise.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet

private theorem faceIntersection_complement {n : ℕ} (t : Finset (Fin (n + 1))) :
    (⨅ j ∈ t, stdSimplex.face.{u} {j}ᶜ) = stdSimplex.face tᶜ := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [stdSimplex.face_univ]
  | @insert j t hj ih =>
    rw [Finset.iInf_insert, ih, stdSimplex.face_inter_face]
    congr 1
    ext k
    simp only [Finset.inf_eq_inter, Finset.mem_inter, Finset.mem_compl, Finset.mem_singleton, Finset.mem_insert, not_or]

private theorem horn_eq_finiteUnion {n : ℕ} (k : Fin (n + 1)) :
    horn.{u} n k = ⨆ j ∈ Finset.univ.erase k, stdSimplex.face {j}ᶜ := by
  rw [horn_eq_iSup]
  ext q x
  simp only [Subfunctor.iSup_obj, Set.mem_iUnion, Subtype.exists,
    Set.mem_compl_iff, Set.mem_singleton_iff, Finset.mem_erase, Finset.mem_univ, and_true]

/-- Every whole original horn preimage is weak when all its complete nonempty
face preimages are weak. All full original simplices are retained. -/
theorem hornPreimage_mem_realizationWeakEquivalences_of_faces {E : SSet.{u}} {n : ℕ}
    (p : E ⟶ (Δ[n + 1] : SSet.{u})) (k : Fin (n + 2))
    (h : ∀ S : Finset (Fin (n + 2)), S.Nonempty →
      realizationWeakEquivalences ((stdSimplex.face S).preimage p).ι) :
    realizationWeakEquivalences ((horn (n + 1) k).preimage p).ι := by
  classical
  let A : Fin (n + 2) → E.Subcomplex := fun j => (stdSimplex.face {j}ᶜ).preimage p
  let s := Finset.univ.erase k
  have hs : s.Nonempty := by
    by_cases hk : k = 0
    · refine ⟨1, ?_⟩
      simp only [s, hk, Finset.mem_erase, Finset.mem_univ, and_true]
      intro heq
      have hv : 1 % (n + 2) = 0 := congrArg Fin.val heq
      rw [Nat.mod_eq_of_lt (by omega : 1 < n + 2)] at hv
      exact Nat.one_ne_zero hv
    · refine ⟨0, ?_⟩
      simp only [s, Finset.mem_erase, Finset.mem_univ, and_true]
      exact Ne.symm hk
  have hU : realizationWeakEquivalences (⨆ j ∈ s, A j).ι := by
    apply Subcomplex.realizationWeakEquivalences_finiteUnion A s hs
    intro t ht htn
    have hk : k ∉ t := by
      intro hkt
      have bad := ht hkt
      exact (Finset.mem_erase.mp bad).1 rfl
    have he := congrArg (fun K : (Δ[n + 1] : SSet.{u}).Subcomplex => K.preimage p)
      (faceIntersection_complement.{u} t)
    simp only [Subcomplex.preimage_iInf_of_sort] at he
    exact (congrArg (fun K : E.Subcomplex => realizationWeakEquivalences K.ι) he).mpr
      (h tᶜ ⟨k, Finset.mem_compl.mpr hk⟩)
  have he := congrArg (fun K : (Δ[n + 1] : SSet.{u}).Subcomplex => K.preimage p)
    (horn_eq_finiteUnion.{u} k)
  simp only [Subcomplex.preimage_iSup_of_sort] at he
  exact (congrArg (fun K : E.Subcomplex => realizationWeakEquivalences K.ι) he).mpr hU

end SSet
