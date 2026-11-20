/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



































































import Mathlib
import Code.Sharpness.Switching
import Code.Walls.gc2_shiftbij
import Code.Ising.AizenmanSignDominance
import Code.Ising.AizenmanInclusionExclusion

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false

namespace StatMech.Walls

open StatMech.Sharpness StatMech.Sharpness.RandomCurrent

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]













theorem gc4_mass_shift_bijOn (ends : ι → Sym2 V) (m K : Finset ι) (hK : K ⊆ m) (S : Finset V) :
    Set.BijOn (fun N => N ∆ K)
      {N | N ⊆ m ∧ sources ends N = S}
      {N | N ⊆ m ∧ sources ends N = S ∆ sources ends K} :=
  gc2_sources_shift_bijOn ends m K hK S





















theorem gc4_aie_mass_shift_invariant (ends : ι → Sym2 V) (m K : Finset ι) (hK : K ⊆ m)
    (S : Finset V) (φ : Finset ι → ℝ)
    (hφ : ∀ N P, P ⊆ m → N ⊆ m → φ (N ∆ P) = φ N) :
    aie_mass ends m φ (S ∆ sources ends K) = aie_mass ends m φ S := by
  unfold aie_mass
  exact asd_switching_weighted_edgecopy ends m K hK S φ (fun N hN => hφ N K hK hN)







theorem gc4_aie_mass_shift_invariant' (ends : ι → Sym2 V) (m K : Finset ι) (hK : K ⊆ m)
    (S : Finset V) (φ : Finset ι → ℝ)
    (hφ : ∀ N P, P ⊆ m → N ⊆ m → φ (N ∆ P) = φ N) :
    aie_mass ends m φ S = aie_mass ends m φ (S ∆ sources ends K) :=
  (gc4_aie_mass_shift_invariant ends m K hK S φ hφ).symm

















theorem gc4_mass_shift_invariant_pair (ends : ι → Sym2 V) (m K : Finset ι) (hK : K ⊆ m)
    (S : Finset V) {u v : V} (hKsrc : sources ends K = {u, v}) (φ : Finset ι → ℝ)
    (hφ : ∀ N P, P ⊆ m → N ⊆ m → φ (N ∆ P) = φ N) :
    aie_mass ends m φ (S ∆ {u, v}) = aie_mass ends m φ S := by
  have h := gc4_aie_mass_shift_invariant ends m K hK S φ hφ
  rwa [hKsrc] at h








theorem gc4_mass_shift_empty (ends : ι → Sym2 V) (m : Finset ι) (S : Finset V) (φ : Finset ι → ℝ)
    (hφ : ∀ N P, P ⊆ m → N ⊆ m → φ (N ∆ P) = φ N) :
    aie_mass ends m φ (S ∆ sources ends (∅ : Finset ι)) = aie_mass ends m φ S :=
  gc4_aie_mass_shift_invariant ends m (∅ : Finset ι) (Finset.empty_subset m) S φ hφ





theorem gc4_mass_self_shift (ends : ι → Sym2 V) (m K : Finset ι) (hK : K ⊆ m) (φ : Finset ι → ℝ)
    (hφ : ∀ N P, P ⊆ m → N ⊆ m → φ (N ∆ P) = φ N) :
    aie_mass ends m φ (sources ends K) = aie_mass ends m φ ∅ := by
  have h := gc4_aie_mass_shift_invariant ends m K hK (∅ : Finset V) φ hφ
  rwa [show (∅ : Finset V) ∆ sources ends K = sources ends K from
    symmDiff_eq_right.mpr rfl] at h

end StatMech.Walls
