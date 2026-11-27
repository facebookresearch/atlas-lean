/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.FieldTheory.Normal.Closure
public import MathlibExt.FieldTheory.Galois.FixingSubgroup
public import MathlibExt.NumberTheory.Padics.PotentiallySemistable
public import MathlibExt.RepresentationTheory.AdmissibleRepresentation.Descent
public import MathlibExt.RingTheory.Perfectoid.DeRhamPeriodRingInvariants

/-!
# de Rham representations over a finite extension

Let `K ⊆ L` be finite extensions of `ℚ_p` inside `ℚ̄_p = PadicAlgCl p`, with `G_L ≤ G_K` the
subgroups `Gal(ℚ̄_p/L) ≤ Gal(ℚ̄_p/K)` (`IntermediateField.fixingSubgroup`), and let `V` be a
representation of `Gal(ℚ̄_p/ℚ_p)`. We prove that `V` is de Rham over `K` if and only if it is
de Rham over `L` (`Representation.isDeRham_iff_of_le`), for de Rham representations as in
J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois representations*, §6.3, Definition 6.27.

When `L/K` is normal (that is, Galois), `G_L` is a normal subgroup of finite index of `G_K`, with
quotient `Gal(L/K)` (`MathlibExt.FieldTheory.Galois.FixingSubgroup`). The rings of invariants are
`B_dR^{G_K} = K` and `B_dR^{G_L} = L` (`PadicComplexInt.fixedPoints_bDeRham_eq_range`;
Fontaine–Ouyang, Proposition 6.26), with `L` embedded in `B_dR` through
`ℚ̄_p ⊆ B_dR^+ ⊆ B_dR`, so `G_K/G_L` acts faithfully on the field `B_dR^{G_L}`, and Galois descent
for admissibility (`Representation.isAdmissible_iff_of_normal`) applies. For general `L`, we pass
through the normal closure of `L` over `ℚ_p` inside `ℚ̄_p`, which is normal over both `K` and `L`.
This is J.-M. Fontaine, *Représentations p-adiques semi-stables*, Astérisque 223 (1994),
Exposé III, §1.8.6 p. 135, for the field `B_dR`, whose invariants are given in *op. cit.*, §3.5
p. 141.

As in `MathlibExt.NumberTheory.Padics.PotentiallySemistable`, no continuity is assumed.
-/

@[expose] public section

open IntermediateField PadicComplexInt

namespace Representation

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]

local notation "𝔹⁺" => BDeRhamPlus 𝓞_ℂ_[p] p
local notation "𝔹" => BDeRham 𝓞_ℂ_[p] p

/-- **de Rham over `K` and over a finite normal extension `L`**: for `K ≤ L` inside `ℚ̄_p` with
`L` finite over `ℚ_p` and `L/K` normal, `V` is de Rham over `K` if and only if it is de Rham over
`L`. -/
private theorem isDeRham_iff_of_normal {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (h : K ≤ L) [FiniteDimensional ℚ_[p] L] [Normal K (extendScalars h)]
    (ρ : Representation ℚ_[p] Gal(PadicAlgCl p/ℚ_[p]) V) :
    ρ.IsDeRham K ↔ ρ.IsDeRham L := by
  have : FiniteDimensional K (extendScalars h) := finiteDimensional_extendScalars h
  have := finiteIndex_subgroupOf_fixingSubgroup h
  rw [IsDeRham, IsDeRham, ← coe_galoisBDeRhamHom]
  refine isAdmissible_iff_of_normal ρ (fixingSubgroup_le h) (normal_subgroupOf_fixingSubgroup h)
    (isRegularPeriodRing_galoisBDeRhamHom p L.fixingSubgroup).isField fun σ _ hσ => ?_
  refine (mem_fixingSubgroup_iff L σ).2 fun y hy => ?_
  have hmem : algebraMap 𝔹⁺ 𝔹 (padicAlgClToBDeRhamPlus p y) ∈
      fixedSubalgebra 𝔹 (galoisBDeRhamHom p) L.fixingSubgroup := fun τ hτ => by
    rw [coe_galoisBDeRhamHom, galoisBDeRham_algebraMap, galoisBDeRhamPlus_padicAlgClToBDeRhamPlus,
      (mem_fixingSubgroup_iff L τ).1 hτ y hy]
  have := hσ _ hmem
  rw [coe_galoisBDeRhamHom, galoisBDeRham_algebraMap,
    galoisBDeRhamPlus_padicAlgClToBDeRhamPlus] at this
  exact padicAlgClToBDeRhamPlus_injective p (algebraMap_bDeRham_injective p this)

/-- **de Rham over `K` and over a finite extension `L`**: for `K ≤ L` inside `ℚ̄_p` with `L`
finite over `ℚ_p`, a representation `V` of `Gal(ℚ̄_p/ℚ_p)` is de Rham over `K` if and only if it
is de Rham over `L`. -/
theorem isDeRham_iff_of_le {K L : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K ≤ L)
    [FiniteDimensional ℚ_[p] L] (ρ : Representation ℚ_[p] Gal(PadicAlgCl p/ℚ_[p]) V) :
    ρ.IsDeRham K ↔ ρ.IsDeRham L := by
  have hLM := le_normalClosure L
  have := normal_extendScalars (h.trans hLM)
  have := normal_extendScalars hLM
  rw [isDeRham_iff_of_normal (h.trans hLM) ρ, isDeRham_iff_of_normal hLM ρ]

end Representation
