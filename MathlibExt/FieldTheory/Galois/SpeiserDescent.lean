/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Ring.Action.Field
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RingTheory.IsGaloisGroup.Defs
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# Speiser's lemma: Galois descent for vector spaces

Let `Γ` be a group acting by ring automorphisms on a commutative ring `L` that is a field
(`IsField L`, so that the results apply to rings of invariants that are fields), and let `W` be an
`L`-module with a **semilinear** action of `Γ`: an additive action with
`g • (a • w) = (g • a) • (g • w)` for `g ∈ Γ`, `a ∈ L` and `w ∈ W`. Write `W^Γ` for the vectors
fixed by `Γ` (`MulAction.fixedPoints Γ W`) and `L^Γ` for the ring of invariants
(`FixedPoints.subring L Γ`).

* `FixedPoints.linearIndependent_of_linearIndependent_subring`: vectors of `W^Γ` that are
  linearly independent over `L^Γ` are linearly independent over `L`. This holds for every group
  `Γ`; the proof is the minimal relation argument, adapted from the proof of
  `Representation.IsRegularPeriodRing.linearIndependent` in
  `MathlibExt.RepresentationTheory.AdmissibleRepresentation.Regular`.
* `FixedPoints.mem_span_of_finiteIndex`: if `Γ` acts on `L` through a finite quotient, that is,
  the kernel `N` of the action on `L` has finite index, then every vector `w` fixed by `N` is an
  `L`-linear combination of vectors of `W^Γ`. Indeed the traces `∑_{q ∈ Γ/N} q • (b • w)` lie in
  `W^Γ`, and by Dedekind's independence of the characters `q : L → L`
  (`linearIndependent_monoidHom`) there are `aⱼ, bⱼ ∈ L` with `∑ⱼ aⱼ q(bⱼ) = 1` for `q = 1` and
  `0` otherwise, so that `w = ∑ⱼ aⱼ ∑_q q • (bⱼ • w)`. In particular, for a finite group acting
  faithfully on `L`, `W^Γ` spans `W` (`FixedPoints.span_eq_top`).

For a finite Galois group `Γ` of a field extension `L/K` (`IsGaloisGroup Γ K L`, for instance
`Γ = Gal(L/K)` for a finite Galois extension `L/K`) acting semilinearly and `K`-linearly on `W`,
these give **Speiser's lemma**: the natural map `L ⊗_K W^Γ → W`, `a ⊗ w ↦ a • w`, is an
isomorphism (`IsGaloisGroup.bijective_liftBaseChange_invariants`,
`IsGaloisGroup.baseChangeInvariantsEquiv`), so that `W^Γ` and `W` have the same dimension
over `K` and `L`; in natural-number form, `finrank K W^Γ = finrank L W`
(`IsGaloisGroup.finrank_invariants`). Here `W^Γ` is the `K`-subspace of invariants of the
representation `Representation.ofDistribMulAction K Γ W`. J.-M. Fontaine,
*Représentations p-adiques semi-stables*, Astérisque 223 (1994), Exposé III, §4.3.1 p. 148,
deduces this from Hilbert's Theorem 90: the natural map `L ⊗_K D_K → D_L` is injective, and
bijective for `L/K` finite. For `W = L ⊗_K U` with the action `σ ⊗ ρ(σ)` induced by a
representation `ρ` of `Gal(L/K)` on a finite-dimensional `K`-vector space `U`, it gives the basis
of invariant vectors of `IsGalois.exists_basis_baseChange_forall_apply_eq_self`.

No topology is involved: the actions are abstract group actions.
-/

@[expose] public section

open scoped TensorProduct
open Module

section Semilinear

variable {Γ L W : Type*} [Group Γ] [CommRing L] [MulSemiringAction Γ L] [AddCommGroup W]
  [Module L W] [DistribMulAction Γ W]

namespace FixedPoints

/-- **Fixed vectors linearly independent over the fixed ring are linearly independent**: let a
group `Γ` act by ring automorphisms on a commutative ring `L` that is a field, and semilinearly on
an `L`-module `W` (`g • (a • w) = (g • a) • (g • w)`). Then a family of vectors of `W` fixed by
`Γ` that is linearly independent over the ring of invariants `L^Γ = FixedPoints.subring L Γ` is
linearly independent over `L`. The minimal relation proof is adapted from that of
`Representation.IsRegularPeriodRing.linearIndependent`. -/
theorem linearIndependent_of_linearIndependent_subring (hL : IsField L)
    (hsl : ∀ (g : Γ) (a : L) (w : W), g • a • w = (g • a) • g • w) {ι : Type*} {v : ι → W}
    (hv : ∀ i (g : Γ), g • v i = v i) (hli : LinearIndependent (FixedPoints.subring L Γ) v) :
    LinearIndependent L v := by
  classical
  let := hL.toField
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
  intro c hc i hi
  by_contra hci
  -- A relation of minimal length is proportional to its conjugates.
  have key : ∀ g : Γ, ∀ j ∈ s, (g • c i) * c j = c i * (g • c j) := by
    intro g
    have h1 : ∑ j ∈ s, (g • c j) • v j = 0 := by
      have := congrArg (g • ·) hc
      simp only [smul_zero, Finset.smul_sum, hsl, hv] at this
      exact this
    let d : ι → L := fun j => (g • c i) * c j - c i * (g • c j)
    have hfull : ∑ j ∈ s, d j • v j = 0 := by
      calc ∑ j ∈ s, d j • v j
          = (g • c i) • ∑ j ∈ s, c j • v j - c i • ∑ j ∈ s, (g • c j) • v j := by
            rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [smul_smul, smul_smul, ← sub_smul]
        _ = 0 := by rw [hc, h1, smul_zero, smul_zero, sub_zero]
    have hd : ∑ j ∈ s.erase i, d j • v j = 0 := by
      rwa [← Finset.add_sum_erase s _ hi, show d i = 0 by simp only [d]; ring, zero_smul,
        zero_add] at hfull
    intro j hj
    by_cases hji : j = i
    · rw [hji, mul_comm]
    · have := ih (s.erase i) (Finset.erase_ssubset hi) d hd j (Finset.mem_erase.2 ⟨hji, hj⟩)
      simp only [d, sub_eq_zero] at this
      exact this
  -- So it is a multiple of a relation with coefficients in the ring of invariants.
  have hgi (g : Γ) : g • c i ≠ 0 := fun h => hci ((smul_eq_zero_iff_eq g).1 h)
  have hfix (j : ι) (hj : j ∈ s) (g : Γ) : g • (c j / c i) = c j / c i := by
    rw [div_eq_mul_inv, smul_mul', smul_inv'', ← div_eq_mul_inv, ← div_eq_mul_inv,
      div_eq_div_iff (hgi g) hci, mul_comm (g • c j), ← key g j hj, mul_comm]
  let e : ι → FixedPoints.subring L Γ := fun j =>
    if hj : j ∈ s then ⟨c j / c i, hfix j hj⟩ else 0
  have h2 : ∑ j ∈ s, e j • v j = 0 := by
    have : ∑ j ∈ s, e j • v j = (c i)⁻¹ • ∑ j ∈ s, c j • v j := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      simp only [e, hj, ↓reduceDIte, Subring.smul_def, smul_smul, div_eq_inv_mul]
    rw [this, hc, smul_zero]
  have hei := congrArg Subtype.val (linearIndependent_iff'.1 hli s e h2 i hi)
  simp only [e, hi, ↓reduceDIte, div_self hci] at hei
  exact one_ne_zero hei

/-- **Fixed vectors span**: let a group `Γ` act by ring automorphisms on a commutative ring `L`
that is a field, and semilinearly on an `L`-module `W` (`g • (a • w) = (g • a) • (g • w)`).
Suppose that the subgroup `N` of the elements of `Γ` acting trivially on `L` has finite index.
Then every vector of `W` fixed by `N` is an `L`-linear combination of vectors fixed by `Γ`. -/
theorem mem_span_of_finiteIndex (hL : IsField L)
    (hsl : ∀ (g : Γ) (a : L) (w : W), g • a • w = (g • a) • g • w) (N : Subgroup Γ)
    [N.FiniteIndex] (hNL : ∀ g : Γ, g ∈ N ↔ ∀ a : L, g • a = a) {w : W}
    (hw : ∀ g ∈ N, g • w = w) : w ∈ Submodule.span L (MulAction.fixedPoints Γ W) := by
  classical
  let := hL.toField
  have : N.Normal := ⟨fun n hn g => (hNL _).2 fun a => by
    rw [mul_smul, mul_smul, (hNL n).1 hn, smul_inv_smul]⟩
  have := Subgroup.finite_quotient_of_finiteIndex (H := N)
  let := Fintype.ofFinite (Γ ⧸ N)
  -- On vectors fixed by `N`, a representative of the class of `g` acts as `g`.
  have hout (g : Γ) {x : W} (hx : ∀ n ∈ N, n • x = x) : (g : Γ ⧸ N).out • x = g • x := by
    obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul N g
    rw [hn, mul_smul, hx n n.2]
  -- The characters of `L` given by the classes of `Γ ⧸ N` are distinct, hence independent.
  let χ : Γ ⧸ N → (L →* L) := fun q => (MulSemiringAction.toRingHom Γ L q.out : L →* L)
  have hχ (q : Γ ⧸ N) (a : L) : χ q a = q.out • a := rfl
  have hχinj : Function.Injective χ := by
    intro q q' h
    have h' (a : L) : q.out • a = q'.out • a := by rw [← hχ, ← hχ, h]
    have hmem : q.out⁻¹ * q'.out ∈ N := (hNL _).2 fun a => by rw [mul_smul, ← h', inv_smul_smul]
    simpa only [QuotientGroup.out_eq'] using QuotientGroup.eq.2 hmem
  have hind : LinearIndependent L fun q : Γ ⧸ N => (χ q : L → L) :=
    (linearIndependent_monoidHom L L).comp χ hχinj
  -- Dedekind's lemma: the vectors `(q • b)_q`, `b ∈ L`, span `L^(Γ ⧸ N)`.
  let v : L → Γ ⧸ N → L := fun b q => q.out • b
  have hspan : Submodule.span L (Set.range v) = ⊤ := by
    rw [← Submodule.dualAnnihilator_eq_bot_iff, eq_bot_iff]
    intro f hf
    rw [Submodule.mem_dualAnnihilator] at hf
    let c : Γ ⧸ N → L := fun i => f fun j => if i = j then 1 else 0
    have hc : ∑ i, c i • (χ i : L → L) = 0 := by
      funext b
      have hb := hf (v b) (Submodule.subset_span ⟨b, rfl⟩)
      rw [LinearMap.pi_apply_eq_sum_univ] at hb
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← hb]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hχ, mul_comm]
      rfl
    have hc0 := Fintype.linearIndependent_iff.1 hind c hc
    rw [Submodule.mem_bot]
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.pi_apply_eq_sum_univ, LinearMap.zero_apply]
    exact Finset.sum_eq_zero fun i _ => by
      rw [show (f fun j => if i = j then 1 else 0) = 0 from hc0 i, smul_zero]
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1
    (hspan ▸ Submodule.mem_top : (fun q : Γ ⧸ N => if q = 1 then (1 : L) else 0) ∈
      Submodule.span L (Set.range v))
  have hcq (q : Γ ⧸ N) : ∑ b ∈ c.support, c b * (q.out • b) = if q = 1 then 1 else 0 := by
    have := congrFun hc q
    simpa only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, v] using this
  -- The trace `∑_q q • x` of a vector `x` fixed by `N` is fixed by `Γ`.
  have hT {x : W} (hx : ∀ n ∈ N, n • x = x) :
      ∑ q : Γ ⧸ N, q.out • x ∈ MulAction.fixedPoints Γ W := fun g => by
    simp only [Finset.smul_sum, ← mul_smul]
    calc ∑ q : Γ ⧸ N, (g * q.out) • x = ∑ q : Γ ⧸ N, ((g : Γ ⧸ N) * q).out • x := by
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [← hout (g * q.out) hx, QuotientGroup.mk_mul, QuotientGroup.out_eq']
      _ = ∑ q : Γ ⧸ N, q.out • x := Fintype.sum_equiv (Equiv.mulLeft (g : Γ ⧸ N)) _ _ fun q => rfl
  -- The vectors `b • w` are fixed by `N`, and `w` is a combination of their traces.
  have hbw (b : L) : ∀ n ∈ N, n • b • w = b • w := fun n hn => by
    rw [hsl, (hNL n).1 hn, hw n hn]
  have hw' : w = ∑ b ∈ c.support, c b • ∑ q : Γ ⧸ N, q.out • b • w := by
    simp only [Finset.smul_sum, hsl, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, hcq, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte]
    rw [← QuotientGroup.mk_one, hout 1 hw, one_smul]
  rw [hw']
  exact Submodule.sum_mem _ fun b _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (hT (hbw b)))

/-- **Fixed vectors span, for a finite group acting faithfully**: for a finite group `Γ` acting
faithfully by ring automorphisms on a commutative ring `L` that is a field, and semilinearly on an
`L`-module `W` (`g • (a • w) = (g • a) • (g • w)`), the vectors of `W` fixed by `Γ` span `W` over
`L`. -/
theorem span_eq_top [Finite Γ] [FaithfulSMul Γ L] (hL : IsField L)
    (hsl : ∀ (g : Γ) (a : L) (w : W), g • a • w = (g • a) • g • w) :
    Submodule.span L (MulAction.fixedPoints Γ W) = ⊤ := by
  have : (⊥ : Subgroup Γ).FiniteIndex := Subgroup.finiteIndex_of_finite
  refine eq_top_iff.2 fun w _ => mem_span_of_finiteIndex hL hsl ⊥
    (fun g => ⟨fun hg a => ?_, fun hg => ?_⟩) fun g hg => ?_
  · rw [Subgroup.mem_bot.1 hg, one_smul]
  · exact Subgroup.mem_bot.2 (FaithfulSMul.eq_of_smul_eq_smul fun a => by rw [hg a, one_smul])
  · rw [Subgroup.mem_bot.1 hg, one_smul]

end FixedPoints

end Semilinear

section Galois

variable {Γ K L W : Type*} [Group Γ] [Field K] [Field L] [Algebra K L] [MulSemiringAction Γ L]
  [AddCommGroup W] [Module L W] [Module K W] [IsScalarTower K L W] [DistribMulAction Γ W]
  [SMulCommClass Γ K W]

namespace Algebra.IsInvariant

/-- **Invariant vectors linearly independent over `K` are linearly independent over `L`**: let
`Γ` act on the field `L` by ring automorphisms such that every element of `L` fixed by `Γ` lies in
the image of `K` (`Algebra.IsInvariant K L Γ`), and semilinearly and `K`-linearly on an
`L`-vector space `W`
(`g • (a • w) = (g • a) • (g • w)`). Then a family of vectors of
`W^Γ = (Representation.ofDistribMulAction K Γ W).invariants` that is linearly independent over
`K` is linearly independent over `L`. -/
theorem linearIndependent_invariants [Algebra.IsInvariant K L Γ]
    (hsl : ∀ (g : Γ) (a : L) (w : W), g • a • w = (g • a) • g • w) {ι : Type*}
    {v : ι → (Representation.ofDistribMulAction K Γ W).invariants}
    (hv : LinearIndependent K v) : LinearIndependent L fun i => (v i : W) := by
  classical
  have hvW : LinearIndependent K fun i => (v i : W) :=
    hv.map' (Representation.ofDistribMulAction K Γ W).invariants.subtype
      (Submodule.ker_subtype _)
  refine FixedPoints.linearIndependent_of_linearIndependent_subring (Field.toIsField L) hsl
    (fun i g => (Representation.mem_invariants _ _).1 (v i).2 g) ?_
  rw [linearIndependent_iff']
  intro s c hc i hi
  choose k hk using fun j => Algebra.IsInvariant.isInvariant (A := K) (G := Γ) (c j : L) (c j).2
  have hks : ∑ j ∈ s, k j • (v j : W) = 0 := by
    rw [← hc]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Subring.smul_def, ← hk j, algebraMap_smul]
  have hk0 := linearIndependent_iff'.1 hvW s k hks i hi
  exact Subtype.ext (by rw [← hk i, hk0, map_zero, ZeroMemClass.coe_zero])

end Algebra.IsInvariant

namespace IsGaloisGroup

/-- **Speiser's lemma** (Galois descent for vector spaces): let `Γ` be a finite Galois group of
the field extension `L/K` (`IsGaloisGroup Γ K L`; for instance `Γ = Gal(L/K)` for a finite
Galois extension `L/K`), and let `Γ` act semilinearly and `K`-linearly on an `L`-vector space `W`
(`g • (a • w) = (g • a) • (g • w)`). Then the natural `L`-linear map
`L ⊗_K W^Γ → W`, `a ⊗ w ↦ a • w`, is bijective, where
`W^Γ = (Representation.ofDistribMulAction K Γ W).invariants`. -/
theorem bijective_liftBaseChange_invariants [Finite Γ] [IsGaloisGroup Γ K L]
    (hsl : ∀ (g : Γ) (a : L) (w : W), g • a • w = (g • a) • g • w) :
    Function.Bijective
      ((Representation.ofDistribMulAction K Γ W).invariants.subtype.liftBaseChange L) := by
  classical
  have : FaithfulSMul Γ L := IsGaloisGroup.faithful K
  set I := (Representation.ofDistribMulAction K Γ W).invariants
  let b := Module.Free.chooseBasis K I
  have hli : LinearIndependent L fun i => (b i : W) :=
    Algebra.IsInvariant.linearIndependent_invariants hsl b.linearIndependent
  have hsp : ⊤ ≤ Submodule.span L (Set.range fun i => (b i : W)) := by
    rw [← FixedPoints.span_eq_top (Field.toIsField L) hsl]
    refine Submodule.span_le.2 fun w hw => ?_
    have hwI : w ∈ I := (Representation.mem_invariants _ w).2 hw
    have h1 := Submodule.mem_map_of_mem (f := I.subtype) (b.mem_span ⟨w, hwI⟩)
    rw [Submodule.map_span, ← Set.range_comp] at h1
    exact Submodule.span_subset_span K L _ h1
  let c := Algebra.TensorProduct.basis L b
  have hφ : I.subtype.liftBaseChange L = (c.equiv (Module.Basis.mk hli hsp)
      (_root_.Equiv.refl _)).toLinearMap :=
    c.ext fun i => by
      rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply]
      simp [c, Algebra.TensorProduct.basis_apply]
  rw [hφ]
  exact (c.equiv _ _).bijective

/-- **Speiser's lemma, as an isomorphism**: for a finite Galois group `Γ` of `L/K` acting
semilinearly and `K`-linearly on an `L`-vector space `W` (`g • (a • w) = (g • a) • (g • w)`), the
natural isomorphism `L ⊗_K W^Γ ≃ W`, `a ⊗ w ↦ a • w`, where
`W^Γ = (Representation.ofDistribMulAction K Γ W).invariants`. -/
noncomputable def baseChangeInvariantsEquiv [Finite Γ] [IsGaloisGroup Γ K L]
    (hsl : ∀ (g : Γ) (a : L) (w : W), g • a • w = (g • a) • g • w) :
    L ⊗[K] (Representation.ofDistribMulAction K Γ W).invariants ≃ₗ[L] W :=
  LinearEquiv.ofBijective _ (bijective_liftBaseChange_invariants hsl)

/-- `baseChangeInvariantsEquiv hsl (a ⊗ w) = a • w`. -/
@[simp]
theorem baseChangeInvariantsEquiv_tmul [Finite Γ] [IsGaloisGroup Γ K L]
    (hsl : ∀ (g : Γ) (a : L) (w : W), g • a • w = (g • a) • g • w) (a : L)
    (w : (Representation.ofDistribMulAction K Γ W).invariants) :
    baseChangeInvariantsEquiv hsl (a ⊗ₜ w) = a • (w : W) :=
  rfl

/-- **Speiser's lemma, dimension form**: for a finite Galois group `Γ` of `L/K` acting
semilinearly and `K`-linearly on an `L`-vector space `W` (`g • (a • w) = (g • a) • (g • w)`),
`finrank K W^Γ = finrank L W` (natural-number dimensions, zero for infinite rank; the
isomorphism `baseChangeInvariantsEquiv` gives the equality of dimensions in general), where
`W^Γ = (Representation.ofDistribMulAction K Γ W).invariants`. -/
theorem finrank_invariants [Finite Γ] [IsGaloisGroup Γ K L]
    (hsl : ∀ (g : Γ) (a : L) (w : W), g • a • w = (g • a) • g • w) :
    finrank K (Representation.ofDistribMulAction K Γ W).invariants = finrank L W := by
  rw [← Module.finrank_baseChange (R := L), (baseChangeInvariantsEquiv hsl).finrank_eq]

end IsGaloisGroup

end Galois
