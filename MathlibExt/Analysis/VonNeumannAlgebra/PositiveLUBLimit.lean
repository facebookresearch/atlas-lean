/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.VonNeumannAlgebra.UltraweakOrder
public import MathlibExt.Analysis.VonNeumannAlgebra.ConjugationPredual
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.ClusterPt

/-!
# Ultraweak limits of bounded increasing positive families

For a concrete von Neumann algebra, a monotone norm-bounded positive family `a_i` with least
upper bound `s` converges ultraweakly to `s` along `atTop`, provided this index filter is
nonbottom.

Fixed star conjugation preserves a supplied least upper bound: the family `x* a_i x` has least
upper bound `x* s x`. This latter statement is given for any preorder-indexed monotone bounded
positive family with the stated least upper bound, without a nonbottom-filter premise.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Set
open scoped Topology

namespace VonNeumannAlgebra

noncomputable section

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {I : Type v} [Preorder I]

/-- **Bounded positive least upper bound is the ultraweak limit.** Let `H` be a complete
complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. let `I` be a preorder
with nonbottom `atTop`, and `a_i ∈ M` a monotone positive family bounded in operator norm.
If `s∈M` is its least upper bound, then `a_i→s` ultraweakly along `atTop`. -/
theorem boundedPositiveIsLUB_tendsto_ultraweak [NeBot (atTop : Filter I)]
    (M : VonNeumannAlgebra H) (a : I → M) (s : M)
    (hmono : @Monotone I M inferInstance (CStarAlgebra.spectralOrder M).toPreorder a)
    (hpositive : ∀ i, @LE.le M (CStarAlgebra.spectralOrder M).toLE 0 (a i))
    (hbound : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C)
    (hLUB : @IsLUB M (CStarAlgebra.spectralOrder M).toLE (Set.range a) s) :
    Tendsto (fun i => (ultraweakLinearEquiv M).symm (a i)) atTop
      (𝓝 ((ultraweakLinearEquiv M).symm s)) := by
  let : PartialOrder (Ultraweak M) := ultraweakPartialOrder M
  let : OrderClosedTopology (Ultraweak M) := ultraweakOrderClosedTopology M
  let f : I → Ultraweak M := fun i => (ultraweakLinearEquiv M).symm (a i)
  have hmonoUL : Monotone f := by
    intro i j hij
    apply (ultraweak_le_iff M (f i) (f j)).mpr
    simpa only [f, LinearEquiv.apply_symm_apply] using hmono hij
  have hLUBUL : IsLUB (Set.range f) ((ultraweakLinearEquiv M).symm s) := by
    constructor
    · rintro _ ⟨i, rfl⟩
      apply (ultraweak_le_iff M (f i) ((ultraweakLinearEquiv M).symm s)).mpr
      simpa only [f, LinearEquiv.apply_symm_apply] using hLUB.1 (Set.mem_range_self i)
    · intro x hx
      apply (ultraweak_le_iff M ((ultraweakLinearEquiv M).symm s) x).mpr
      change @LE.le M (CStarAlgebra.spectralOrder M).toLE s (ultraweakLinearEquiv M x)
      apply hLUB.2
      rintro _ ⟨i, rfl⟩
      have h := (ultraweak_le_iff M (f i) x).mp (hx (Set.mem_range_self i))
      simpa only [f, LinearEquiv.apply_symm_apply] using h
  obtain ⟨C, hC⟩ := hbound
  let K : Set (Ultraweak M) := Ici (0 : Ultraweak M) ∩
    {x | ‖ultraweakLinearEquiv M x‖ ≤ C}
  have hcompact : IsCompact K := (ultraweakClosedBall_isCompact M C).inter_left isClosed_Ici
  have hmem : ∀ᶠ i in atTop, f i ∈ K := Eventually.of_forall fun i => by
    constructor
    · apply (ultraweak_le_iff M 0 (f i)).mpr
      simpa only [f, map_zero, LinearEquiv.apply_symm_apply] using hpositive i
    · change ‖ultraweakLinearEquiv M ((ultraweakLinearEquiv M).symm (a i))‖ ≤ C
      simpa only [LinearEquiv.apply_symm_apply] using hC i
  have hunique (y : Ultraweak M) (_hy : y ∈ K) (hy : MapClusterPt y atTop f) :
      y = (ultraweakLinearEquiv M).symm s := by
    have hycluster : ClusterPt y (Filter.map f atTop) := hy
    apply le_antisymm
    · have hupper : Iic ((ultraweakLinearEquiv M).symm s) ∈ Filter.map f atTop :=
        Filter.mem_map.mpr (Eventually.of_forall fun i => hLUBUL.1 (Set.mem_range_self i))
      exact isClosed_Iic.mem_of_nhdsWithin_neBot
        (hycluster.mono (le_principal_iff.mpr hupper))
    · apply hLUBUL.2
      rintro _ ⟨i, rfl⟩
      have hlower : Ici (f i) ∈ Filter.map f atTop :=
        Filter.mem_map.mpr ((eventually_ge_atTop i).mono fun j hij => hmonoUL hij)
      exact isClosed_Ici.mem_of_nhdsWithin_neBot
        (hycluster.mono (le_principal_iff.mpr hlower))
  obtain ⟨y, hy, hycluster⟩ := hcompact.exists_mapClusterPt (u := f) (f := (atTop : Filter I))
    (le_principal_iff.mpr (Filter.mem_map.mpr hmem))
  have hyeq := hunique y hy hycluster
  have hlimit : Tendsto f atTop (𝓝 y) :=
    hcompact.tendsto_nhds_of_unique_mapClusterPt hmem
      (fun z hz hzcluster => (hunique z hz hzcluster).trans hyeq.symm)
  simpa only [hyeq, f] using hlimit

variable [IsDirectedOrder I] [Nonempty I]

/-- **Fixed star conjugation preserves a bounded positive least upper bound.** Let `H` be a
complete complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. for any
preorder `I`, monotone norm-bounded positive family `a_i`, its least upper bound `s`, and
`x∈M`, the element `x* s x` is the least upper bound of `{x* a_i x}`. No nonbottom `atTop`
condition is assumed in this statement. -/
theorem starConjugation_preserves_boundedPositiveIsLUB (M : VonNeumannAlgebra H) (x : M)
    (a : I → M) (s : M)
    (hmono : @Monotone I M inferInstance (CStarAlgebra.spectralOrder M).toPreorder a)
    (hpositive : ∀ i, @LE.le M (CStarAlgebra.spectralOrder M).toLE 0 (a i))
    (hbound : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C)
    (hLUB : @IsLUB M (CStarAlgebra.spectralOrder M).toLE (Set.range a) s) :
    @IsLUB M (CStarAlgebra.spectralOrder M).toLE
      (Set.range fun i => star x * a i * x) (star x * s * x) := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M
  let : PartialOrder (Ultraweak M) := ultraweakPartialOrder M
  let : OrderClosedTopology (Ultraweak M) := ultraweakOrderClosedTopology M
  let f : I → Ultraweak M := fun i => (ultraweakLinearEquiv M).symm (star x * a i * x)
  let t : Ultraweak M := (ultraweakLinearEquiv M).symm (star x * s * x)
  have ha := boundedPositiveIsLUB_tendsto_ultraweak M a s hmono hpositive hbound hLUB
  have hc := (ultraweak_starConjugation_continuous M x).tendsto
    ((ultraweakLinearEquiv M).symm s) |>.comp ha
  have hlimit : Tendsto f atTop (𝓝 t) := by
    rw [Function.comp_def] at hc
    simpa only [f, t, LinearEquiv.apply_symm_apply] using hc
  have hleSource : ∀ i, @LE.le M (CStarAlgebra.spectralOrder M).toLE
      (star x * a i * x) (star x * s * x) := fun i =>
    star_left_conjugate_le_conjugate (hLUB.1 (Set.mem_range_self i)) x
  have hle : ∀ i, f i ≤ t := fun i => by
    apply (ultraweak_le_iff M (f i) t).mpr
    simpa only [f, t, LinearEquiv.apply_symm_apply] using hleSource i
  have ht : IsLUB (Set.range f) t := IsLUB.range_of_tendsto hle hlimit
  constructor
  · rintro _ ⟨i, rfl⟩
    exact hleSource i
  · intro b hb
    have hbUL : (ultraweakLinearEquiv M).symm b ∈ upperBounds (Set.range f) := by
      rintro _ ⟨i, rfl⟩
      apply (ultraweak_le_iff M (f i) ((ultraweakLinearEquiv M).symm b)).mpr
      simpa only [f, LinearEquiv.apply_symm_apply] using hb (Set.mem_range_self i)
    have h := (ultraweak_le_iff M t ((ultraweakLinearEquiv M).symm b)).mp (ht.2 hbUL)
    simpa only [t, LinearEquiv.apply_symm_apply] using h

end

end VonNeumannAlgebra
