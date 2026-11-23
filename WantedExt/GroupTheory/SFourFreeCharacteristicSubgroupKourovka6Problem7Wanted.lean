/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A characteristic subgroup for S₄-free groups (Kourovka Notebook Problem 6.7)

Kourovka Notebook, Archive of Solved Problems, Problem 6.7 (G. Glauberman): suppose that P is a
finite 2-group. Does there exist a characteristic subgroup L(P) of P such that L(P) is normal in H
for every finite group H that satisfies the following conditions: 1) P is a Sylow 2-subgroup of H,
2) H is S₄-free, and 3) C_H(O₂(H)) ≤ O₂(H)?
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.GroupTheory.BaerSuzukiWanted

@[expose] public section

namespace MathlibExt.GroupTheory.SFourFreeCharacteristicSubgroupKourovka6Problem7Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 6.7 (G.
Glauberman). UnsolvedMath record UM-00700354 (`KOU-6.7`), dataset ulamai/UnsolvedMath v1.8.0.

`L(P)` must be non-trivial for non-trivial `P` (`L(P) = 1` satisfies the rest), as in Stellmacher's
theorem. `P` is a Sylow `2`-subgroup of `H` through an injective homomorphism `ι : P →* H` whose
range is a Sylow `2`-subgroup. `S₄`-free means that no section `K ⧸ L` is isomorphic to `S₄`;
`O₂(H)` is `pCore 2 H` of the Baer-Suzuki module, the largest normal `2`-subgroup.
-/

open MathlibExt.GroupTheory.BaerSuzukiWanted.GroupTheory.Defs (pCore)

/-- `H` is `S₄`-free: no section `K ⧸ L` of `H` is isomorphic to the symmetric group `S₄`. -/
def IsSFourFree (H : Type) [Group H] : Prop :=
  ¬ ∃ (K : Subgroup H) (L : Subgroup K) (_ : L.Normal), Nonempty (K ⧸ L ≃* Equiv.Perm (Fin 4))

/-- Kourovka 6.7 (G. Glauberman): every non-trivial finite `2`-group `P` has a non-trivial
characteristic subgroup `L(P)` that is normal in every finite `S₄`-free group `H` having `P` as a
Sylow `2`-subgroup and satisfying `C_H(O₂(H)) ≤ O₂(H)`, where `O₂(H) = pCore 2 H`. -/
def sFourFreeCharacteristicSubgroup : Prop :=
  ∀ (P : Type) [Group P] [Finite P], IsPGroup 2 P → Nontrivial P →
    ∃ L : Subgroup P, L.Characteristic ∧ L ≠ ⊥ ∧
      ∀ (H : Type) [Group H] [Finite H] (ι : P →* H), Function.Injective ι →
        (∃ S : Sylow 2 H, (S : Subgroup H) = ι.range) → IsSFourFree H →
        Subgroup.centralizer (pCore 2 H : Set H) ≤ pCore 2 H → (L.map ι).Normal

/--
Resolved true: Stellmacher (1996) proves that every finite non-trivial `2`-group `S` has a
non-trivial characteristic subgroup `W(S)` that is normal in every finite `Σ₄`-free group `H` with
`S ∈ Syl₂(H)` and `C_H(O₂(H)) ≤ O₂(H)`, and the Kourovka Archive answers 6.7 "Yes, there does".
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 6.7 (G.
Glauberman); resolution: B. Stellmacher, A characteristic subgroup of Σ4-free groups, Israel J.
Math. 94 (1996), 367-379, Abstract: for a finite non-trivial 2-group S there is a nontrivial
characteristic subgroup W(S) of S which is normal in every finite Σ4-free group H with S ∈ Syl₂(H)
and C_H(O₂(H)) ≤ O₂(H); Kourovka Archive, Problem 6.7: Yes, there does,
https://doi.org/10.1007/BF02762712.
-/
public theorem_wanted sFourFreeCharacteristicSubgroup_holds : sFourFreeCharacteristicSubgroup

end MathlibExt.GroupTheory.SFourFreeCharacteristicSubgroupKourovka6Problem7Wanted
