/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.RepresentationTheory.AdmissibleRepresentation
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Admissible representations for a regular ring of periods

Let `F` be a field and `G` a group acting on a commutative `F`-algebra `S` by `F`-algebra
automorphisms, through a homomorphism `act : G →* (S →ₐ[F] S)` (each `act g` is invertible, with
inverse `act g⁻¹`): an `(F, G)`-ring in the sense of J.-M. Fontaine, *Représentations p-adiques
semi-stables*, Astérisque 223 (1994), Exposé III, §1.3.1 p. 121. Let `H` be a subgroup of `G` and
`E = S^H`. Following J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois representations*,
§3.1, Definition 3.9, the ring `S` is **`(F, H)`-regular** (`Representation.IsRegularPeriodRing`)
if

* (i) `S` is a domain (the hypothesis `[IsDomain S]`);
* (ii) `S^H = (Frac S)^H`, for the action of `G` on the fraction field of `S` that extends `act`
  (`Representation.fractionRingAction`, `Representation.IsRegularPeriodRing.image_fixedSubalgebra`);
* (iii) every nonzero `b ∈ S` such that the line `F b` is stable under `H` is a unit.

Then `E` is a field (`Representation.IsRegularPeriodRing.isField`; Fontaine, *op. cit.*, §1.4.1
p. 122), and every `(F, G)`-ring that is a field is regular
(`Representation.isRegularPeriodRing_of_isField`; *op. cit.*, Proposition 1.6.1 p. 125).

For a regular ring we prove Theorem 3.14 (1) of Fontaine–Ouyang (Fontaine, *op. cit.*,
Proposition 1.4.2 p. 123): for every representation `V` of `G`,

* the comparison map `α_V : S ⊗_E D_S(V) → S ⊗_F V` is injective
  (`Representation.IsRegularPeriodRing.comparison_injective`), because vectors of `D_S(V)` that are
  linearly independent over `E` are linearly independent over `S`
  (`Representation.IsRegularPeriodRing.linearIndependent`);
* `dim_E D_S(V) ≤ dim_F V` if `V` is finite-dimensional
  (`Representation.IsRegularPeriodRing.finrank_periods_le`);
* equality holds if and only if `α_V` is an isomorphism, that is, `V` is `S`-admissible in the
  sense of Fontaine (*op. cit.*, Definition 1.5.1 p. 124)
  (`Representation.IsRegularPeriodRing.finrank_periods_eq_iff`,
  `Representation.IsRegularPeriodRing.isAdmissible_iff_comparison_bijective`), and if and only if
  `S ⊗_F V` has an `S`-basis of `H`-fixed vectors
  (`Representation.IsRegularPeriodRing.isAdmissible_iff_hasFixedBasis`).

So for a regular ring the three forms of admissibility of
`MathlibExt.RepresentationTheory.AdmissibleRepresentation` agree. The injectivity is Fontaine's
minimal relation argument (*op. cit.*, §1.6.2 p. 125), with coefficients in `S` rather than in a
field, using (ii); the case of equality is his determinant argument (*op. cit.*, §1.4.3 p. 123),
using (iii). Fontaine's own definition of a `G`-regular ring (*op. cit.*, §1.4.1 p. 122) asks
instead that `S` be nonzero and reduced and that every `α_V` be injective, together with (iii).

Only abstract group actions occur: no topology is involved and continuity is never assumed.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Representation

variable {F G S V : Type*} [Field F] [Group G] [CommRing S] [Algebra F S] [AddCommGroup V]
  [Module F V]

/-- An action of a group by algebra maps acts by injective maps: `act g⁻¹` is a left inverse of
`act g`. -/
private theorem act_injective (act : G →* (S →ₐ[F] S)) (g : G) : Function.Injective (act g) :=
  Function.LeftInverse.injective (g := act g⁻¹) fun x => by
    rw [← AlgHom.mul_apply, ← map_mul, inv_mul_cancel, map_one, AlgHom.one_apply]

/-- The coordinates of `(act g ⊗ id) y` in the basis `(1 ⊗ vₖ)` of `S ⊗_F V` are the images by
`act g` of those of `y`. -/
private theorem repr_rTensor_apply {ι : Type*} (act : G →* (S →ₐ[F] S)) (g : G)
    (v : Module.Basis ι F V) (y : S ⊗[F] V) (k : ι) :
    (Algebra.TensorProduct.basis S v).repr ((act g).toLinearMap.rTensor V y) k =
      act g ((Algebra.TensorProduct.basis S v).repr y k) := by
  induction y using TensorProduct.inductionOn with
  | tmul s w =>
    simp [Algebra.TensorProduct.basis_repr_tmul]
  | add y z hy hz => simp only [map_add, Finsupp.add_apply, hy, hz]

/-- **The determinant of `σ_g ∘ x`**: for the basis `e = (1 ⊗ vₖ)` of `S ⊗_F V` and the diagonal
action `σ_g = act g ⊗ ρ g`, `e.det (σ_g ∘ x) = det (ρ g) • act g (e.det x)`. -/
private theorem det_map_comp {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : Representation F G V)
    (act : G →* (S →ₐ[F] S)) (g : G) (v : Module.Basis ι F V) (x : ι → S ⊗[F] V) :
    (Algebra.TensorProduct.basis S v).det (TensorProduct.map (act g).toLinearMap (ρ g) ∘ x) =
      algebraMap F S (LinearMap.det (ρ g)) * act g ((Algebra.TensorProduct.basis S v).det x) := by
  have : Module.Finite F V := Module.Finite.of_basis v
  set e := Algebra.TensorProduct.basis S v
  have hσ : (TensorProduct.map (act g).toLinearMap (ρ g) : S ⊗[F] V → S ⊗[F] V) =
      (ρ g).baseChange S ∘ (act g).toLinearMap.rTensor V := by
    ext y
    rw [← LinearMap.lTensor_comp_rTensor, LinearMap.coe_comp, LinearMap.baseChange_eq_lTensor]
  rw [hσ, Function.comp_assoc, e.det_comp, LinearMap.det_baseChange, e.det_apply, e.det_apply,
    (act g).map_det]
  congr 2
  ext k i
  simp only [Module.Basis.toMatrix_apply, Function.comp_apply, AlgHom.mapMatrix_apply,
    Matrix.map_apply]
  exact repr_rTensor_apply act g v (x i) k

/-! ### Regular rings -/

section Regular

variable [IsDomain S]

/-- **The action of `G` on the fraction field of `S`** that extends an action `act` of `G` on the
domain `S` by `F`-algebra maps: `act g` is an automorphism of `S`, with inverse `act g⁻¹`, and
extends to the automorphism `a / s ↦ act g a / act g s` of `Frac S`. -/
def fractionRingAction (act : G →* (S →ₐ[F] S)) : G →* (FractionRing S ≃ₐ[F] FractionRing S) :=
  (IsFractionRing.fieldEquivOfAlgEquivHom F (FractionRing S)).comp
    ((AlgEquiv.algHomUnitsEquiv F S).toMonoidHom.comp act.toHomUnits)

/-- `fractionRingAction act g` extends `act g`. -/
@[simp]
theorem fractionRingAction_algebraMap (act : G →* (S →ₐ[F] S)) (g : G) (s : S) :
    fractionRingAction act g (algebraMap S (FractionRing S) s) =
      algebraMap S (FractionRing S) (act g s) := by
  simp only [fractionRingAction, MonoidHom.coe_comp, Function.comp_apply,
    IsFractionRing.fieldEquivOfAlgEquivHom_apply, IsFractionRing.fieldEquivOfAlgEquiv_algebraMap]
  rfl

/-- **`S` is `(F, H)`-regular** (Fontaine–Ouyang, Definition 3.9), for a domain `S` (condition (i))
with an action `act` of `G` by `F`-algebra maps and a subgroup `H` of `G`:

* (ii) `S^H = (Frac S)^H`: every element of the fraction field of `S` fixed by `H` lies in `S`;
* (iii) every nonzero `b ∈ S` such that the line `F b` is stable under `H` is a unit. -/
structure IsRegularPeriodRing (act : G →* (S →ₐ[F] S)) (H : Subgroup G) : Prop where
  /-- Condition (ii): every element of the fraction field of `S` fixed by every `g ∈ H` lies in
  the image of `S`. -/
  mem_range_of_forall_eq : ∀ x : FractionRing S, (∀ g ∈ H, fractionRingAction act g x = x) →
    x ∈ (algebraMap S (FractionRing S)).range
  /-- Condition (iii): every nonzero `b ∈ S` such that `act g b ∈ F b` for every `g ∈ H` is a
  unit. -/
  isUnit_of_forall_mem_span : ∀ b : S, b ≠ 0 → (∀ g ∈ H, act g b ∈ F ∙ b) → IsUnit b

/-- **A field is regular** (Fontaine, Exposé III, Proposition 1.6.1 p. 125): an `(F, G)`-ring that
is a field is `(F, H)`-regular for every subgroup `H`. -/
theorem isRegularPeriodRing_of_isField (hS : IsField S) (act : G →* (S →ₐ[F] S))
    (H : Subgroup G) : IsRegularPeriodRing act H where
  mem_range_of_forall_eq x _ := by
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj (nonZeroDivisors S) x
    obtain ⟨t, ht⟩ := hS.mul_inv_cancel (nonZeroDivisors.coe_ne_zero s)
    refine ⟨a * t, ?_⟩
    have hs : algebraMap S (FractionRing S) s * algebraMap S (FractionRing S) t = 1 := by
      rw [← map_mul, ht, map_one]
    rw [map_mul, ← h, mul_assoc, hs, mul_one]
  isUnit_of_forall_mem_span b hb _ := by
    obtain ⟨t, ht⟩ := hS.mul_inv_cancel hb
    exact ⟨⟨b, t, ht, by rw [mul_comm]; exact ht⟩, rfl⟩

namespace IsRegularPeriodRing

variable {act : G →* (S →ₐ[F] S)} {H : Subgroup G}

/-- **Condition (ii) says `S^H = (Frac S)^H`**: the image of `S^H` in the fraction field is the set
of elements fixed by every `g ∈ H`. -/
theorem image_fixedSubalgebra (hS : IsRegularPeriodRing act H) :
    algebraMap S (FractionRing S) '' (fixedSubalgebra S act H : Set S) =
      {x | ∀ g ∈ H, fractionRingAction act g x = x} := by
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩ g hg
    rw [fractionRingAction_algebraMap, mem_fixedSubalgebra.1 hs g hg]
  · intro hx
    obtain ⟨s, rfl⟩ := hS.mem_range_of_forall_eq x hx
    refine ⟨s, mem_fixedSubalgebra.2 fun g hg => IsFractionRing.injective S (FractionRing S) ?_,
      rfl⟩
    rw [← fractionRingAction_algebraMap, hx g hg]

/-- **The ring of invariants of a regular ring is a field** (Fontaine, Exposé III, §1.4.1 p. 122):
a nonzero `b ∈ S^H` spans an `H`-stable line, so it is a unit of `S`, and its inverse is
invariant. -/
theorem isField (hS : IsRegularPeriodRing act H) : IsField (fixedSubalgebra S act H) where
  exists_pair_ne := ⟨0, 1, zero_ne_one⟩
  mul_comm := mul_comm
  mul_inv_cancel {b} hb := by
    have hb' : (b : S) ≠ 0 := fun h => hb (Subtype.ext h)
    obtain ⟨u, hu⟩ := hS.isUnit_of_forall_mem_span b hb' fun g hg => by
      rw [mem_fixedSubalgebra.1 b.2 g hg]
      exact Submodule.mem_span_singleton_self _
    refine ⟨⟨↑u⁻¹, mem_fixedSubalgebra.2 fun g hg => ?_⟩, Subtype.ext ?_⟩
    · have h1 : act g (↑u⁻¹ : S) * (u : S) = 1 := by
        rw [hu, ← mem_fixedSubalgebra.1 b.2 g hg, ← map_mul, ← hu, Units.inv_mul, map_one]
      calc act g (↑u⁻¹ : S) = act g (↑u⁻¹ : S) * ((u : S) * ↑u⁻¹) := by
            rw [Units.mul_inv, mul_one]
        _ = ↑u⁻¹ := by rw [← mul_assoc, h1, one_mul]
    · simp [← hu]

/-- **The field `S^H`** of a regular ring `S`. -/
abbrev field (hS : IsRegularPeriodRing act H) : Field (fixedSubalgebra S act H) :=
  hS.isField.toField

/-- For a regular ring `S`, `D_S(V)` is a free module over the field `S^H`. -/
theorem free_periods (hS : IsRegularPeriodRing act H) (ρ : Representation F G V) :
    Module.Free (fixedSubalgebra S act H) (ρ.periods act H) := by
  let := hS.field
  exact Module.Free.of_divisionRing (fixedSubalgebra S act H) (ρ.periods act H)

/-- **Condition (ii) without fractions**: if `a, s ∈ S` with `s ≠ 0` and `a / s` is `H`-invariant,
that is, `act g a * s = a * act g s` for every `g ∈ H`, then `a = e * s` for some `e ∈ S^H`. -/
theorem exists_mem_fixedSubalgebra_eq_mul (hS : IsRegularPeriodRing act H) {a s : S} (hs : s ≠ 0)
    (h : ∀ g ∈ H, act g a * s = a * act g s) : ∃ e ∈ fixedSubalgebra S act H, a = e * s := by
  have hinj := IsFractionRing.injective S (FractionRing S)
  have hgs : ∀ g, act g s ≠ 0 := fun g => (map_ne_zero_iff _ (act_injective act g)).2 hs
  have hs' : algebraMap S (FractionRing S) s ≠ 0 := (map_ne_zero_iff _ hinj).2 hs
  obtain ⟨e, he⟩ := hS.mem_range_of_forall_eq
    (algebraMap S (FractionRing S) a / algebraMap S (FractionRing S) s) fun g hg => by
      rw [map_div₀, fractionRingAction_algebraMap, fractionRingAction_algebraMap,
        div_eq_div_iff ((map_ne_zero_iff _ hinj).2 (hgs g)) hs', ← map_mul, ← map_mul, h g hg]
  have hae : a = e * s := hinj (by rw [map_mul, he, div_mul_cancel₀ _ hs'])
  refine ⟨e, mem_fixedSubalgebra.2 fun g hg => ?_, hae⟩
  have h' := h g hg
  rw [hae, map_mul] at h'
  exact mul_right_cancel₀ (mul_ne_zero (hgs g) hs) (by rw [← mul_assoc, h']; ring)

/-- **Vectors of `D_S(V)` linearly independent over `S^H` are linearly independent over `S`** in
`S ⊗_F V`, for a regular ring `S` (Fontaine–Ouyang, Theorem 3.14 (1); Fontaine, Exposé III,
§1.6.2 p. 125, for a field). -/
theorem linearIndependent (hS : IsRegularPeriodRing act H) (ρ : Representation F G V)
    {ι : Type*} {v : ι → ρ.periods act H}
    (hv : LinearIndependent (fixedSubalgebra S act H) v) :
    LinearIndependent S fun i => (v i : S ⊗[F] V) := by
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
  intro c hc i hi
  by_contra hci
  -- A relation of minimal length is proportional to its conjugates.
  have key : ∀ g ∈ H, ∀ j ∈ s, act g (c j) * c i = c j * act g (c i) := by
    intro g hg
    have h1 : ∑ j ∈ s, act g (c j) • (v j : S ⊗[F] V) = 0 := by
      have := congrArg (TensorProduct.map (act g).toLinearMap (ρ g)) hc
      rw [map_sum, map_zero] at this
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul_tmul, mem_periods.1 (v j).2 g hg]
    let d : ι → S := fun j => act g (c i) * c j - c i * act g (c j)
    have hfull : ∑ j ∈ s, d j • (v j : S ⊗[F] V) = 0 := by
      calc ∑ j ∈ s, d j • (v j : S ⊗[F] V)
          = act g (c i) • ∑ j ∈ s, c j • (v j : S ⊗[F] V) -
            c i • ∑ j ∈ s, act g (c j) • (v j : S ⊗[F] V) := by
            rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [smul_smul, smul_smul, ← sub_smul]
        _ = 0 := by rw [hc, h1, smul_zero, smul_zero, sub_zero]
    have hd : ∑ j ∈ s.erase i, d j • (v j : S ⊗[F] V) = 0 := by
      rwa [← Finset.add_sum_erase s _ hi, show d i = 0 by simp only [d]; ring, zero_smul,
        zero_add] at hfull
    intro j hj
    by_cases hji : j = i
    · rw [hji, mul_comm]
    · have := ih (s.erase i) (Finset.erase_ssubset hi) d hd j (Finset.mem_erase.2 ⟨hji, hj⟩)
      simp only [d, sub_eq_zero] at this
      linear_combination -this
  -- So it is a multiple of a relation with coefficients in `S^H`.
  choose e he hce using fun j (hj : j ∈ s) =>
    hS.exists_mem_fixedSubalgebra_eq_mul hci fun g hg => key g hg j hj
  let f : ι → fixedSubalgebra S act H := fun j =>
    if hj : j ∈ s then ⟨e j hj, he j hj⟩ else 0
  have h2 : c i • ∑ j ∈ s, (f j : S) • (v j : S ⊗[F] V) = 0 := by
    rw [Finset.smul_sum, ← hc]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [f, hj, ↓reduceDIte, smul_smul]
    rw [hce j hj, mul_comm]
  have h3 : ∑ j ∈ s, (f j : S) • (v j : S ⊗[F] V) = 0 := (smul_eq_zero.1 h2).resolve_left hci
  have hfi : f i = 0 := linearIndependent_iff'ₛ.1 hv s f 0 (by
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero]
    apply Subtype.ext
    rw [Submodule.coe_sum, Submodule.coe_zero, ← h3]
    exact Finset.sum_congr rfl fun j _ => by rw [Submodule.coe_smul, Subalgebra.smul_def]) i hi
  have he1 : e i hi = 1 := mul_right_cancel₀ hci (by rw [one_mul, ← hce i hi])
  simp only [f, hi, ↓reduceDIte] at hfi
  have h0 := congrArg Subtype.val hfi
  rw [ZeroMemClass.coe_zero] at h0
  exact one_ne_zero (he1.symm.trans h0)

/-- **`α_V` is injective for a regular ring** (Fontaine–Ouyang, Theorem 3.14 (1)): the `S`-basis
`1 ⊗ dᵢ` of `S ⊗_{S^H} D_S(V)` given by an `S^H`-basis `(dᵢ)` of `D_S(V)` is mapped to the
`S`-linearly independent family `(dᵢ)`. -/
theorem comparison_injective (hS : IsRegularPeriodRing act H) (ρ : Representation F G V) :
    Function.Injective (ρ.comparison act H) := by
  have := hS.free_periods ρ
  let b := Module.Free.chooseBasis (fixedSubalgebra S act H) (ρ.periods act H)
  let c := Algebra.TensorProduct.basis S b
  have hli : LinearIndependent S (ρ.comparison act H ∘ c) := by
    convert hS.linearIndependent ρ b.linearIndependent using 1
    ext i
    simp [c, Algebra.TensorProduct.basis_apply]
  intro x y hxy
  refine c.repr.injective (hli ?_)
  rw [← Finsupp.apply_linearCombination, ← Finsupp.apply_linearCombination,
    c.linearCombination_repr, c.linearCombination_repr, hxy]

/-- For a regular ring `S` and a finite-dimensional `V`, `D_S(V)` is finite-dimensional over
`S^H`. -/
theorem finite_periods (hS : IsRegularPeriodRing act H) (ρ : Representation F G V)
    [FiniteDimensional F V] : Module.Finite (fixedSubalgebra S act H) (ρ.periods act H) := by
  have := hS.free_periods ρ
  let b := Module.Free.chooseBasis (fixedSubalgebra S act H) (ρ.periods act H)
  have := (hS.linearIndependent ρ b.linearIndependent).finite
  exact Module.Finite.of_basis b

/-- **`dim_{S^H} D_S(V) ≤ dim_F V` for a regular ring** (Fontaine–Ouyang, Theorem 3.14 (1);
Fontaine, Exposé III, Proposition 1.4.2 (i) p. 123). -/
theorem finrank_periods_le (hS : IsRegularPeriodRing act H) (ρ : Representation F G V)
    [FiniteDimensional F V] :
    Module.finrank (fixedSubalgebra S act H) (ρ.periods act H) ≤ Module.finrank F V := by
  have := hS.free_periods ρ
  let b := Module.Free.chooseBasis (fixedSubalgebra S act H) (ρ.periods act H)
  have hli := hS.linearIndependent ρ b.linearIndependent
  have := hli.finite
  let := Fintype.ofFinite (Module.Free.ChooseBasisIndex (fixedSubalgebra S act H)
    (ρ.periods act H))
  rw [Module.finrank_eq_card_basis b, ← Module.finrank_baseChange (R := S) (S := F) (M' := V)]
  exact hli.fintype_card_le_finrank

/-- **The equality case for a regular ring** (Fontaine, Exposé III, §1.4.3 p. 123): if
`dim_{S^H} D_S(V) = dim_F V`, then an `S^H`-basis `(dᵢ)` of `D_S(V)` is an `S`-basis of `S ⊗_F V`.
Indeed, the determinant `δ` of `(dᵢ)` in a basis `1 ⊗ vᵢ` is nonzero, and
`act g δ = det (ρ g)⁻¹ • δ`, so `δ` spans an `H`-stable line and is a unit by (iii). -/
theorem hasFixedBasis_of_isAdmissible (hS : IsRegularPeriodRing act H) {ρ : Representation F G V}
    (h : ρ.IsAdmissible act H) : ρ.HasFixedBasis act H := by
  classical
  obtain ⟨hV, hd⟩ := h
  have := hS.free_periods ρ
  have := hS.finite_periods ρ
  let bE := Module.finBasisOfFinrankEq (fixedSubalgebra S act H) (ρ.periods act H) hd
  let x : Fin (Module.finrank F V) → S ⊗[F] V := fun i => bE i
  have hx : LinearIndependent S x := hS.linearIndependent ρ bE.linearIndependent
  let e := Algebra.TensorProduct.basis S (Module.finBasis F V)
  have hdet : IsUnit (e.det x) := by
    refine hS.isUnit_of_forall_mem_span _ (fun h0 => ?_) fun g hg => ?_
    · rw [Module.Basis.det_apply] at h0
      obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
      refine hw0 (funext (Fintype.linearIndependent_iff.1 hx w (e.repr.injective ?_)))
      ext k
      have hk : ∑ i, e.repr (x i) k * w i = 0 := by
        simpa [Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply] using congrFun hw k
      rw [map_sum, map_zero, Finsupp.finsetSum_apply, Finsupp.zero_apply, ← hk]
      exact Finset.sum_congr rfl fun i _ => by
        rw [map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
    · have hfix : TensorProduct.map (act g).toLinearMap (ρ g) ∘ x = x :=
        funext fun i => mem_periods.1 (bE i).2 g hg
      have h1 := det_map_comp ρ act g (Module.finBasis F V) x
      rw [hfix] at h1
      change e.det x = algebraMap F S (LinearMap.det (ρ g)) * act g (e.det x) at h1
      have hunit : LinearMap.det (ρ g) * LinearMap.det (ρ g⁻¹) = 1 := by
        rw [← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one]
      refine Submodule.mem_span_singleton.2 ⟨LinearMap.det (ρ g⁻¹), ?_⟩
      rw [Algebra.smul_def]
      calc algebraMap F S (LinearMap.det (ρ g⁻¹)) * e.det x
          = algebraMap F S (LinearMap.det (ρ g⁻¹)) *
            (algebraMap F S (LinearMap.det (ρ g)) * act g (e.det x)) := by rw [← h1]
        _ = act g (e.det x) := by
          rw [← mul_assoc, ← map_mul, mul_comm (LinearMap.det (ρ g⁻¹)), hunit, map_one, one_mul]
  obtain ⟨hli, hsp⟩ := e.is_basis_iff_det.2 hdet
  exact ⟨_, Module.Basis.mk hli hsp.ge, fun i => by rw [Module.Basis.mk_apply]; exact (bE i).2⟩

/-- **Admissibility for a regular ring, dimension and basis forms** (Fontaine, Exposé III,
Proposition 1.4.2 p. 123): for a finite-dimensional `V`, `dim_{S^H} D_S(V) = dim_F V` if and only
if `S ⊗_F V` has an `S`-basis of `H`-fixed vectors. -/
theorem isAdmissible_iff_hasFixedBasis (hS : IsRegularPeriodRing act H)
    (ρ : Representation F G V) [FiniteDimensional F V] :
    ρ.IsAdmissible act H ↔ ρ.HasFixedBasis act H :=
  ⟨hS.hasFixedBasis_of_isAdmissible, HasFixedBasis.isAdmissible⟩

/-- **Admissibility for a regular ring** (Fontaine–Ouyang, Theorem 3.14 (1); Fontaine, Exposé III,
Proposition 1.4.2 p. 123 and Definition 1.5.1 p. 124): for a finite-dimensional `V`,
`dim_{S^H} D_S(V) = dim_F V` if and only if `α_V : S ⊗_{S^H} D_S(V) → S ⊗_F V` is an
isomorphism, that is, `V` is `S`-admissible. -/
theorem isAdmissible_iff_comparison_bijective (hS : IsRegularPeriodRing act H)
    (ρ : Representation F G V) [FiniteDimensional F V] :
    ρ.IsAdmissible act H ↔ Function.Bijective (ρ.comparison act H) := by
  have := hS.free_periods ρ
  exact ⟨fun h => (hS.hasFixedBasis_of_isAdmissible h).comparison_bijective,
    fun h => (hasFixedBasis_of_comparison_bijective h).isAdmissible⟩

/-- **Equality in `dim_{S^H} D_S(V) ≤ dim_F V` holds exactly when `α_V` is an isomorphism**, for a
regular ring and a finite-dimensional `V` (Fontaine–Ouyang, Theorem 3.14 (1)). -/
theorem finrank_periods_eq_iff (hS : IsRegularPeriodRing act H) (ρ : Representation F G V)
    [FiniteDimensional F V] :
    Module.finrank (fixedSubalgebra S act H) (ρ.periods act H) = Module.finrank F V ↔
      Function.Bijective (ρ.comparison act H) := by
  rw [← hS.isAdmissible_iff_comparison_bijective ρ, IsAdmissible, and_iff_right ‹_›]

/-- For a regular ring and a finite-dimensional `V`, `α_V` is an isomorphism if and only if
`S ⊗_F V` has an `S`-basis of `H`-fixed vectors. -/
theorem hasFixedBasis_iff_comparison_bijective (hS : IsRegularPeriodRing act H)
    (ρ : Representation F G V) [FiniteDimensional F V] :
    ρ.HasFixedBasis act H ↔ Function.Bijective (ρ.comparison act H) :=
  (hS.isAdmissible_iff_hasFixedBasis ρ).symm.trans (hS.isAdmissible_iff_comparison_bijective ρ)

end IsRegularPeriodRing

end Regular

end Representation
