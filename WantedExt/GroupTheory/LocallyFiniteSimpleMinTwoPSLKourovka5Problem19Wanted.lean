/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Simple locally finite groups with the min-2 condition (Kourovka Notebook Problem 5.19)

Kourovka Notebook, Archive of Solved Problems, Problem 5.19 (O. H. Kegel): a) let G be an infinite
locally finite simple group satisfying the minimum condition for 2-subgroups; is G = PSL_2(F), F
some locally finite field of odd characteristic, if the centralizer of every involution of G is
almost locally soluble? b) Can one characterize the simple locally finite groups with the min-2
condition containing a maximal radical non-trivial 2-subgroup of rank ≤ 2 as linear groups of small
rank?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.PGroup
public import WantedExt.GroupTheory.CentralizerDimensionSocleQuotientKourovka19Problem101Wanted
public import WantedExt.GroupTheory.GroupClassesShared
public import WantedExt.GroupTheory.InvolutionCentralizerPSLTwoKourovka18Problem59Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.LocallyFiniteSimpleMinTwoPSLKourovka5Problem19Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.19 (O. H.
Kegel). UnsolvedMath record UM-00700303 (`KOU-5.19`), dataset ulamai/UnsolvedMath v1.8.0.

Only part (a) is formalized; part (b) asks for a characterization ("as linear groups of small rank")
with no precise target. The minimum condition for `2`-subgroups is stated as the descending chain
condition on `2`-subgroups (equivalent). Almost locally soluble: a locally soluble subgroup of
finite index (finitely generated subgroups soluble). A locally finite field has all finitely
generated subfields finite. Locally finite groups, locally soluble subgroups and locally finite
fields are `IsLocallyFinite` of `GroupClassesShared`, `IsLocallySoluble` of the Kourovka 19.101
entry and `IsLocallyFiniteField` of the Kourovka 18.59 entry, reused here; odd characteristic is
`ringChar F ≠ 2` (a locally finite field has prime characteristic). `PSL₂(F)` is Mathlib's
`Matrix.ProjectiveSpecialLinearGroup (Fin 2) F`.
-/

open MathlibExt.GroupTheory.CentralizerDimensionSocleQuotientKourovka19Problem101Wanted
  (IsLocallySoluble)
open MathlibExt.GroupTheory.InvolutionCentralizerPSLTwoKourovka18Problem59Wanted
  (IsLocallyFiniteField)
open MathlibExt.GroupTheory.GroupClassesShared (IsLocallyFinite)

/-- Kourovka 5.19(a) (O. H. Kegel): an infinite locally finite simple group `G` satisfying the
minimum condition for `2`-subgroups (no strictly descending infinite chain of `2`-subgroups), in
which the centralizer of every involution is almost locally soluble (has a locally soluble subgroup
of finite index), is isomorphic to `PSL₂(F)` for a locally finite field `F` of odd
characteristic. -/
def minTwoSimpleIsPSLTwo : Prop :=
  ∀ (G : Type) [Group G] [IsSimpleGroup G] [Infinite G], IsLocallyFinite G →
    (∀ f : ℕ → Subgroup G, (∀ n, IsPGroup 2 (f n)) → (∀ n, f (n + 1) ≤ f n) →
      ∃ N, ∀ n ≥ N, f n = f N) →
    (∀ i : G, orderOf i = 2 → ∃ H : Subgroup G, H ≤ Subgroup.centralizer {i} ∧
      H.relIndex (Subgroup.centralizer {i}) ≠ 0 ∧ IsLocallySoluble H) →
    ∃ (F : Type) (_ : Field F), IsLocallyFiniteField F ∧ ringChar F ≠ 2 ∧
      Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)

/--
Resolved true: the Kourovka Archive answers 5.19(a) "Yes, it is", citing Chernikov, Simple locally
finite groups with the minimality condition for 2-subgroups (Ukrainian Math. J. 35 (1983), 230-231).
Part (b), a request for a characterization, is not formalized. Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.19 (O. H. Kegel); resolution: N. S.
Chernikov, Simple locally finite groups with the minimality condition for 2-subgroups, Ukrainian
Math. J. 35 (1983), 230-231, Kourovka Archive, Problem 5.19: a) Yes, it is (Chernikov),
https://doi.org/10.1007/BF01088944.
-/
public theorem_wanted minTwoSimpleIsPSLTwo_holds : minTwoSimpleIsPSLTwo

end MathlibExt.GroupTheory.LocallyFiniteSimpleMinTwoPSLKourovka5Problem19Wanted
