/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.FieldTheory.Galois.SpeiserDescent
public import MathlibExt.RepresentationTheory.AdmissibleRepresentation.Regular

/-!
# Galois descent for admissibility

Let `F` be a field and `G` a group acting on a commutative `F`-algebra `S` by `F`-algebra maps
through a homomorphism `act : G →* (S →ₐ[F] S)`, and let `ρ` be a representation of `G` on an
`F`-vector space `V`. Let `H' ≤ H` be subgroups of `G`, with `E = S^H` and `L = S^{H'}`
(`Representation.fixedSubalgebra`), so that `E ⊆ L` (`Representation.fixedSubalgebra_antitone`)
and `D_{S,H}(V) ⊆ D_{S,H'}(V)` (`Representation.periods_subset_periods`).

Suppose that `H'` is normal in `H` and of finite index, that `L` is a field, and that `H/H'` acts
faithfully on `L`: every `h ∈ H` fixing `L` pointwise lies in `H'`. Then `H` acts on the field `L`
through the finite group `H/H'`, with fixed field `E`; by Artin's theorem `L/E` is then a finite
Galois extension with group `H/H'`, which need not be assumed. The group `H` also acts
semilinearly on the `L`-module `S ⊗_F V`, the vectors fixed by `H'` form `D_{S,H'}(V)`, and those
fixed by `H`, that is, the invariants of `H/H'` in `D_{S,H'}(V)`, form `D_{S,H}(V)`. Speiser's
lemma in the form of `MathlibExt.FieldTheory.Galois.SpeiserDescent` gives:

* `Representation.linearIndependent_periods_of_normal`: vectors of `D_{S,H}(V)` linearly
  independent over `E` are linearly independent over `L` (here only the normality of `H'` and the
  field `L` are used);
* `Representation.span_periods_of_normal`: `D_{S,H}(V)` spans `D_{S,H'}(V)` over `L`;
* `Representation.periodsBasisOfNormal`: an `E`-basis of `D_{S,H}(V)` is an `L`-basis of
  `D_{S,H'}(V)`; equivalently, the natural map `L ⊗_E D_{S,H}(V) → D_{S,H'}(V)` is an isomorphism
  (`Representation.periodsBaseChangeEquiv`);
* `Representation.rank_periods_eq_of_normal`, `Representation.finrank_periods_eq_of_normal`:
  `dim_E D_{S,H}(V) = dim_L D_{S,H'}(V)`, so `V` is admissible for `H` if and only if it is
  admissible for `H'` (`Representation.isAdmissible_iff_of_normal`, in the dimension form of
  `Representation.IsAdmissible`);
* for a ring `S` that is `(F, H')`-regular (`Representation.IsRegularPeriodRing`; J.-M. Fontaine
  and Y. Ouyang, *Theory of p-adic Galois representations*, §3.1, Definition 3.9), and hence
  `(F, H)`-regular (`Representation.IsRegularPeriodRing.mono`), the same holds for the basis form
  and for the comparison map `α_V`
  (`Representation.IsRegularPeriodRing.hasFixedBasis_iff_of_normal`,
  `Representation.IsRegularPeriodRing.comparison_bijective_iff_of_normal`).

This is J.-M. Fontaine, *Représentations p-adiques semi-stables*, Astérisque 223 (1994),
Exposé III, §1.8.6 p. 135, where `H = Gal(K̄/L)`, `H' = Gal(K̄/L')` for a finite Galois extension
`L'/L` and `J = H/H'` acts faithfully on `F_{L'} = B^{H'}`: a representation that becomes
`B`-admissible over `L'` was already `B`-admissible over `L`. The formula
`D_{B,L'}(V) = F_{L'} ⊗_{F_L} D_{B,L}(V)` appears in *op. cit.*, §1.8.5 p. 135, for `V` that
becomes `B`-admissible over `L`; here it holds for every `V`.

As in `MathlibExt.RepresentationTheory.AdmissibleRepresentation`, the actions are abstract group
actions: no topology is involved.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Representation

variable {F G S V : Type*} [Field F] [Group G] [CommRing S] [Algebra F S] [AddCommGroup V]
  [Module F V]

/-! ### Monotonicity in the subgroup -/

/-- **`S^H ⊆ S^{H'}` for `H' ≤ H`**: the ring of invariants is antitone in the subgroup. -/
theorem fixedSubalgebra_antitone (act : G → S →ₐ[F] S) : Antitone (fixedSubalgebra S act) :=
  fun _ _ h _ hs g hg => hs g (h hg)

/-- **`D_{S,H}(V) ⊆ D_{S,H'}(V)` for `H' ≤ H`**, as subsets of `S ⊗_F V`. -/
theorem periods_subset_periods (ρ : Representation F G V) (act : G → S →ₐ[F] S)
    {H H' : Subgroup G} (h : H' ≤ H) :
    (ρ.periods act H : Set (S ⊗[F] V)) ⊆ ρ.periods act H' :=
  fun _ hx g hg => hx g (h hg)

/-- **`S^H` is a field if `S^{H'}` is**, for `H' ≤ H`: the inverse in `S^{H'}` of a nonzero
element of `S^H` is fixed by `H`. -/
theorem isField_fixedSubalgebra_of_le {act : G → S →ₐ[F] S} {H H' : Subgroup G} (h : H' ≤ H)
    (hL : IsField (fixedSubalgebra S act H')) : IsField (fixedSubalgebra S act H) where
  exists_pair_ne := ⟨0, 1, fun h0 => hL.exists_pair_ne.elim fun a ha => by
    obtain ⟨b, hb⟩ := ha
    exact hb (Subtype.ext (by
      have h1 : (1 : S) = 0 := (congrArg Subtype.val h0).symm
      rw [← mul_one (a : S), ← mul_one (b : S), h1, mul_zero, mul_zero]))⟩
  mul_comm := mul_comm
  mul_inv_cancel {e} he := by
    have he' : (⟨e, fixedSubalgebra_antitone act h e.2⟩ : fixedSubalgebra S act H') ≠ 0 :=
      fun h0 => he (Subtype.ext
        (congrArg (fun x : fixedSubalgebra S act H' => (x : S)) h0 : _))
    obtain ⟨y, hy⟩ := hL.mul_inv_cancel he'
    have hy' : (e : S) * y = 1 := congrArg Subtype.val hy
    refine ⟨⟨y, fun g hg => ?_⟩, Subtype.ext hy'⟩
    calc act g y = act g y * ((e : S) * y) := by rw [hy', mul_one]
      _ = (act g y * act g e) * y := by rw [e.2 g hg, mul_assoc]
      _ = y := by rw [← map_mul, mul_comm (y : S), hy', map_one, one_mul]

/-! ### Descent along a normal subgroup of finite index -/

section Descent

variable {act : G →* (S →ₐ[F] S)} {H H' : Subgroup G}

/-- For `H'` normal in `H` and `h ∈ H`, the element `h⁻¹ n h` lies in `H'` for `n ∈ H'`. -/
private theorem inv_mul_mul_mem (hle : H' ≤ H) (hN : (H'.subgroupOf H).Normal) {h n : G}
    (hh : h ∈ H) (hn : n ∈ H') : h⁻¹ * n * h ∈ H' := by
  have := (Subgroup.normal_subgroupOf_iff hle).1 hN n h⁻¹ hn (H.inv_mem hh)
  rwa [inv_inv] at this

/-- For `H'` normal in `H`, the action of `h ∈ H` on `S` preserves `S^{H'}`. -/
private theorem act_mem_fixedSubalgebra (hle : H' ≤ H) (hN : (H'.subgroupOf H).Normal) {h : G}
    (hh : h ∈ H) {x : S} (hx : x ∈ fixedSubalgebra S act H') :
    act h x ∈ fixedSubalgebra S act H' := fun n hn => by
  rw [← AlgHom.mul_apply, ← map_mul, show n * h = h * (h⁻¹ * n * h) by group, map_mul,
    AlgHom.mul_apply, hx _ (inv_mul_mul_mem hle hN hh hn)]

/-- The diagonal action of `G` on `S ⊗_F V` is multiplicative. -/
private theorem map_mul_apply (ρ : Representation F G V) (g k : G) (x : S ⊗[F] V) :
    TensorProduct.map (act (g * k)).toLinearMap (ρ (g * k)) x =
      TensorProduct.map (act g).toLinearMap (ρ g)
        (TensorProduct.map (act k).toLinearMap (ρ k) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s v => simp [map_mul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The diagonal action of `1 ∈ G` on `S ⊗_F V` is the identity. -/
private theorem map_one_apply (ρ : Representation F G V) (x : S ⊗[F] V) :
    TensorProduct.map (act 1).toLinearMap (ρ 1) x = x := by
  induction x using TensorProduct.inductionOn with
  | tmul s v => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The action of `H` on `S^{H'}` by ring automorphisms, for `H'` normal in `H`. -/
private abbrev fixedSubalgebraAction (hle : H' ≤ H) (hN : (H'.subgroupOf H).Normal) :
    MulSemiringAction H (fixedSubalgebra S act H') where
  smul h x := ⟨act h x, act_mem_fixedSubalgebra hle hN h.2 x.2⟩
  one_smul x := Subtype.ext (show act 1 (x : S) = x by simp)
  mul_smul h k x := Subtype.ext (show act ((h : G) * k) (x : S) = act h (act k x) by simp)
  smul_zero _ := Subtype.ext (map_zero _)
  smul_add _ _ _ := Subtype.ext (map_add _ _ _)
  smul_one _ := Subtype.ext (map_one _)
  smul_mul _ _ _ := Subtype.ext (map_mul _ _ _)

/-- The diagonal action of `H` on `S ⊗_F V`. -/
private abbrev tensorAction (ρ : Representation F G V) (H : Subgroup G) :
    DistribMulAction H (S ⊗[F] V) where
  smul h x := TensorProduct.map (act h).toLinearMap (ρ h) x
  one_smul := map_one_apply (act := act) ρ
  mul_smul h k := map_mul_apply (act := act) ρ h k
  smul_zero _ := map_zero _
  smul_add _ := map_add _

/-- **Vectors of `D_{S,H}(V)` linearly independent over `S^H` are linearly independent over
`S^{H'}`** in `S ⊗_F V`, for `H' ≤ H` normal in `H` such that `S^{H'}` is a field: `H` acts on the
field `S^{H'}`, with fixed ring `S^H`, and semilinearly on `S ⊗_F V`, with invariants
`D_{S,H}(V)`. -/
theorem linearIndependent_periods_of_normal (ρ : Representation F G V) (hle : H' ≤ H)
    (hN : (H'.subgroupOf H).Normal) (hL : IsField (fixedSubalgebra S act H')) {ι : Type*}
    {v : ι → ρ.periods act H} (hv : LinearIndependent (fixedSubalgebra S act H) v) :
    LinearIndependent (fixedSubalgebra S act H') fun i => (v i : S ⊗[F] V) := by
  classical
  let := fixedSubalgebraAction (act := act) hle hN
  let := tensorAction (act := act) ρ H
  have hsl (g : H) (a : fixedSubalgebra S act H') (x : S ⊗[F] V) : g • a • x = (g • a) • g • x :=
    map_smul_tmul ρ act g a x
  have hw (i : ι) (g : H) : g • (v i : S ⊗[F] V) = v i := (v i).2 g g.2
  refine FixedPoints.linearIndependent_of_linearIndependent_subring hL hsl hw
    (linearIndependent_iff'ₛ.2 fun s c c' hc i hi => ?_)
  have hcH (c : ι → FixedPoints.subring (fixedSubalgebra S act H') H) (j : ι) :
      ((c j : fixedSubalgebra S act H') : S) ∈ fixedSubalgebra S act H :=
    fun g hg => congrArg Subtype.val ((c j).2 ⟨g, hg⟩)
  let k (c : ι → FixedPoints.subring (fixedSubalgebra S act H') H) (j : ι) :
      fixedSubalgebra S act H := ⟨_, hcH c j⟩
  have hk : ∑ j ∈ s, k c j • v j = ∑ j ∈ s, k c' j • v j :=
    Subtype.ext (by simp only [Submodule.coe_sum]; exact hc)
  have hk0 := congrArg (fun x : fixedSubalgebra S act H => (x : S))
    (linearIndependent_iff'ₛ.1 hv s (k c) (k c') hk i hi)
  exact Subtype.ext (Subtype.ext hk0)

/-- **`D_{S,H}(V)` spans `D_{S,H'}(V)` over `S^{H'}`**, for `H' ≤ H` normal in `H` and of finite
index such that `S^{H'}` is a field on which `H/H'` acts faithfully, that is, every `h ∈ H`
fixing `S^{H'}` pointwise lies in `H'`. -/
theorem span_periods_of_normal (ρ : Representation F G V) (hle : H' ≤ H)
    (hN : (H'.subgroupOf H).Normal) [(H'.subgroupOf H).FiniteIndex]
    (hL : IsField (fixedSubalgebra S act H'))
    (hfaithful : ∀ h ∈ H, (∀ x ∈ fixedSubalgebra S act H', act h x = x) → h ∈ H') :
    Submodule.span (fixedSubalgebra S act H') (ρ.periods act H : Set (S ⊗[F] V)) =
      ρ.periods act H' := by
  classical
  let := fixedSubalgebraAction (act := act) hle hN
  let := tensorAction (act := act) ρ H
  have hsl (g : H) (a : fixedSubalgebra S act H') (x : S ⊗[F] V) : g • a • x = (g • a) • g • x :=
    map_smul_tmul ρ act g a x
  have hfix : MulAction.fixedPoints H (S ⊗[F] V) = (ρ.periods act H : Set (S ⊗[F] V)) :=
    Set.ext fun x => ⟨fun h g hg => h ⟨g, hg⟩, fun h g => h g g.2⟩
  refine le_antisymm (Submodule.span_le.2 (periods_subset_periods ρ act hle)) fun x hx => ?_
  rw [← hfix]
  refine FixedPoints.mem_span_of_finiteIndex hL hsl (H'.subgroupOf H)
    (fun g => ⟨fun hg (a : fixedSubalgebra S act H') =>
        Subtype.ext (mem_fixedSubalgebra.1 a.2 g (Subgroup.mem_subgroupOf.1 hg)),
      fun h => Subgroup.mem_subgroupOf.2
        (hfaithful g g.2 fun y hy => congrArg Subtype.val (h ⟨y, hy⟩))⟩)
    fun g hg => mem_periods.1 hx g (Subgroup.mem_subgroupOf.1 hg)

/-- **An `S^H`-basis of `D_{S,H}(V)` is an `S^{H'}`-basis of `D_{S,H'}(V)`**, for `H' ≤ H` normal
in `H` and of finite index such that `S^{H'}` is a field on which `H/H'` acts faithfully (every
`h ∈ H` fixing `S^{H'}` pointwise lies in `H'`). This is the statement that the natural map
`S^{H'} ⊗_{S^H} D_{S,H}(V) → D_{S,H'}(V)` is an isomorphism
(`Representation.periodsBaseChangeEquiv`). -/
def periodsBasisOfNormal (ρ : Representation F G V) (hle : H' ≤ H)
    (hN : (H'.subgroupOf H).Normal) [(H'.subgroupOf H).FiniteIndex]
    (hL : IsField (fixedSubalgebra S act H'))
    (hfaithful : ∀ h ∈ H, (∀ x ∈ fixedSubalgebra S act H', act h x = x) → h ∈ H') {ι : Type*}
    (b : Module.Basis ι (fixedSubalgebra S act H) (ρ.periods act H)) :
    Module.Basis ι (fixedSubalgebra S act H') (ρ.periods act H') :=
  Module.Basis.mk (v := fun i => ⟨b i, periods_subset_periods ρ act hle (b i).2⟩)
    (LinearIndependent.of_comp (ρ.periods act H').subtype
      (linearIndependent_periods_of_normal ρ hle hN hL b.linearIndependent))
    (by
      intro x _
      have hD : (ρ.periods act H : Set (S ⊗[F] V)) ⊆
          Submodule.span (fixedSubalgebra S act H') (Set.range fun i => (b i : S ⊗[F] V)) := by
        intro y hy
        have h1 : y ∈ Submodule.span (fixedSubalgebra S act H)
            (Set.range fun i => (b i : S ⊗[F] V)) := by
          have := Submodule.mem_map_of_mem (f := (ρ.periods act H).subtype) (b.mem_span ⟨y, hy⟩)
          rwa [Submodule.map_span, ← Set.range_comp] at this
        clear hy
        induction h1 using Submodule.span_induction with
        | mem z hz => exact Submodule.subset_span hz
        | zero => exact Submodule.zero_mem _
        | add z z' _ _ hz hz' => exact Submodule.add_mem _ hz hz'
        | smul e z _ hz =>
          exact Submodule.smul_mem _
            (⟨e, fixedSubalgebra_antitone act hle e.2⟩ : fixedSubalgebra S act H') hz
      have hx : (x : S ⊗[F] V) ∈
          Submodule.span (fixedSubalgebra S act H') (Set.range fun i => (b i : S ⊗[F] V)) := by
        refine Submodule.span_le.2 hD ?_
        rw [span_periods_of_normal ρ hle hN hL hfaithful]
        exact x.2
      rw [show (fun i => (b i : S ⊗[F] V)) = (ρ.periods act H').subtype ∘
          fun i => (⟨b i, periods_subset_periods ρ act hle (b i).2⟩ : ρ.periods act H') from rfl,
        Set.range_comp, ← Submodule.map_span] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      rwa [Subtype.ext hyx] at hy)

/-- The vectors of `periodsBasisOfNormal ρ hle hN hL hfaithful b` are those of `b`. -/
@[simp]
theorem coe_periodsBasisOfNormal (ρ : Representation F G V) (hle : H' ≤ H)
    (hN : (H'.subgroupOf H).Normal) [(H'.subgroupOf H).FiniteIndex]
    (hL : IsField (fixedSubalgebra S act H'))
    (hfaithful : ∀ h ∈ H, (∀ x ∈ fixedSubalgebra S act H', act h x = x) → h ∈ H') {ι : Type*}
    (b : Module.Basis ι (fixedSubalgebra S act H) (ρ.periods act H)) (i : ι) :
    (periodsBasisOfNormal ρ hle hN hL hfaithful b i : S ⊗[F] V) = b i := by
  simp [periodsBasisOfNormal]

/-- **Galois descent for the rank of `D_S(V)`**: `rank_{S^H} D_{S,H}(V) =
rank_{S^{H'}} D_{S,H'}(V)`, for `H' ≤ H` normal in `H` and of finite index such that `S^{H'}` is a
field on which `H/H'` acts faithfully (every `h ∈ H` fixing `S^{H'}` pointwise lies in `H'`). -/
theorem rank_periods_eq_of_normal (ρ : Representation F G V) (hle : H' ≤ H)
    (hN : (H'.subgroupOf H).Normal) [(H'.subgroupOf H).FiniteIndex]
    (hL : IsField (fixedSubalgebra S act H'))
    (hfaithful : ∀ h ∈ H, (∀ x ∈ fixedSubalgebra S act H', act h x = x) → h ∈ H') :
    Module.rank (fixedSubalgebra S act H) (ρ.periods act H) =
      Module.rank (fixedSubalgebra S act H') (ρ.periods act H') := by
  let := (isField_fixedSubalgebra_of_le hle hL).toField
  let := hL.toField
  have := Module.Free.of_divisionRing (fixedSubalgebra S act H) (ρ.periods act H)
  let b := Module.Free.chooseBasis (fixedSubalgebra S act H) (ρ.periods act H)
  rw [← b.mk_eq_rank'', ← (periodsBasisOfNormal ρ hle hN hL hfaithful b).mk_eq_rank'']

/-- **Galois descent for the dimension of `D_S(V)`**: `dim_{S^H} D_{S,H}(V) =
dim_{S^{H'}} D_{S,H'}(V)`, for `H' ≤ H` normal in `H` and of finite index such that `S^{H'}` is a
field on which `H/H'` acts faithfully (every `h ∈ H` fixing `S^{H'}` pointwise lies in `H'`). -/
theorem finrank_periods_eq_of_normal (ρ : Representation F G V) (hle : H' ≤ H)
    (hN : (H'.subgroupOf H).Normal) [(H'.subgroupOf H).FiniteIndex]
    (hL : IsField (fixedSubalgebra S act H'))
    (hfaithful : ∀ h ∈ H, (∀ x ∈ fixedSubalgebra S act H', act h x = x) → h ∈ H') :
    Module.finrank (fixedSubalgebra S act H) (ρ.periods act H) =
      Module.finrank (fixedSubalgebra S act H') (ρ.periods act H') :=
  congrArg Cardinal.toNat (rank_periods_eq_of_normal ρ hle hN hL hfaithful)

/-- **Galois descent for admissibility, dimension form** (Fontaine, Exposé III, §1.8.6 p. 135):
`V` is admissible for `S` as a representation of `H` if and only if it is admissible as a
representation of `H'`, for `H' ≤ H` normal in `H` and of finite index such that `S^{H'}` is a
field on which `H/H'` acts faithfully (every `h ∈ H` fixing `S^{H'}` pointwise lies in `H'`). -/
theorem isAdmissible_iff_of_normal (ρ : Representation F G V) (hle : H' ≤ H)
    (hN : (H'.subgroupOf H).Normal) [(H'.subgroupOf H).FiniteIndex]
    (hL : IsField (fixedSubalgebra S act H'))
    (hfaithful : ∀ h ∈ H, (∀ x ∈ fixedSubalgebra S act H', act h x = x) → h ∈ H') :
    ρ.IsAdmissible act H ↔ ρ.IsAdmissible act H' := by
  rw [IsAdmissible, IsAdmissible, finrank_periods_eq_of_normal ρ hle hN hL hfaithful]

/-! ### The base change isomorphism -/

variable (act) in
/-- **`S^{H'}` as an algebra over `S^H`**, for `H' ≤ H`, through the inclusion `S^H ⊆ S^{H'}`
(`Representation.fixedSubalgebra_antitone`). -/
abbrev fixedSubalgebraAlgebra (hle : H' ≤ H) :
    Algebra (fixedSubalgebra S act H) (fixedSubalgebra S act H') :=
  (Subalgebra.inclusion (fixedSubalgebra_antitone act hle)).toRingHom.toAlgebra

/-- **`D_S(V)` is free over `S^H` when `S^H` is a field.** -/
theorem free_periods_of_isField (ρ : Representation F G V)
    (hE : IsField (fixedSubalgebra S act H)) :
    Module.Free (fixedSubalgebra S act H) (ρ.periods act H) := by
  let := hE.toField
  exact Module.Free.of_divisionRing (fixedSubalgebra S act H) (ρ.periods act H)

/-- **Galois descent for `D_S(V)`, tensor form**: for `H' ≤ H` normal in `H` and of finite index
such that `S^{H'}` is a field on which `H/H'` acts faithfully (every `h ∈ H` fixing `S^{H'}`
pointwise lies in `H'`), the natural map `S^{H'} ⊗_{S^H} D_{S,H}(V) → D_{S,H'}(V)`,
`a ⊗ x ↦ a • x`, is an isomorphism of `S^{H'}`-modules. Here `S^{H'}` is an `S^H`-algebra
through the inclusion (`Representation.fixedSubalgebraAlgebra`). Fontaine (Exposé III, §1.8.5
p. 135) states this isomorphism for `V` admissible for `H`. -/
def periodsBaseChangeEquiv (ρ : Representation F G V) (hle : H' ≤ H)
    (hN : (H'.subgroupOf H).Normal) [(H'.subgroupOf H).FiniteIndex]
    (hL : IsField (fixedSubalgebra S act H'))
    (hfaithful : ∀ h ∈ H, (∀ x ∈ fixedSubalgebra S act H', act h x = x) → h ∈ H') :
    letI := fixedSubalgebraAlgebra act hle
    fixedSubalgebra S act H' ⊗[fixedSubalgebra S act H] ρ.periods act H ≃ₗ[fixedSubalgebra S act H']
      ρ.periods act H' :=
  letI := fixedSubalgebraAlgebra act hle
  haveI : IsScalarTower (fixedSubalgebra S act H) (fixedSubalgebra S act H') (S ⊗[F] V) :=
    ⟨fun e a x => mul_smul (e : S) (a : S) x⟩
  haveI := free_periods_of_isField ρ (isField_fixedSubalgebra_of_le hle hL)
  let φ := LinearMap.codRestrict (ρ.periods act H')
    ((ρ.periods act H).subtype.liftBaseChange (fixedSubalgebra S act H')) fun y => by
      induction y using TensorProduct.inductionOn with
      | tmul a x =>
        rw [LinearMap.liftBaseChange_tmul]
        exact Submodule.smul_mem _ a (periods_subset_periods ρ act hle x.2)
      | add y z hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  LinearEquiv.ofBijective φ (by
    let b := Module.Free.chooseBasis (fixedSubalgebra S act H) (ρ.periods act H)
    let c := Algebra.TensorProduct.basis (fixedSubalgebra S act H') b
    have : φ = (c.equiv (periodsBasisOfNormal ρ hle hN hL hfaithful b)
        (_root_.Equiv.refl _)).toLinearMap :=
      c.ext fun i => by
        rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply]
        refine Subtype.ext ?_
        simp [φ, c, Algebra.TensorProduct.basis_apply]
    rw [this]
    exact (c.equiv _ _).bijective)

/-- `periodsBaseChangeEquiv ρ hle hN hL hfaithful (a ⊗ x) = a • x`. -/
@[simp]
theorem coe_periodsBaseChangeEquiv_tmul (ρ : Representation F G V) (hle : H' ≤ H)
    (hN : (H'.subgroupOf H).Normal) [(H'.subgroupOf H).FiniteIndex]
    (hL : IsField (fixedSubalgebra S act H'))
    (hfaithful : ∀ h ∈ H, (∀ x ∈ fixedSubalgebra S act H', act h x = x) → h ∈ H')
    (a : fixedSubalgebra S act H') (x : ρ.periods act H) :
    letI := fixedSubalgebraAlgebra act hle
    (periodsBaseChangeEquiv ρ hle hN hL hfaithful (a ⊗ₜ x) : S ⊗[F] V) = a • (x : S ⊗[F] V) :=
  rfl

/-! ### Regular rings -/

section Regular

variable [IsDomain S]

/-- **Regularity for a subgroup implies regularity for a larger subgroup**: if `S` is
`(F, H')`-regular and `H' ≤ H`, then `S` is `(F, H)`-regular. -/
theorem IsRegularPeriodRing.mono (hS : IsRegularPeriodRing act H') (h : H' ≤ H) :
    IsRegularPeriodRing act H where
  mem_range_of_forall_eq x hx := hS.mem_range_of_forall_eq x fun g hg => hx g (h hg)
  isUnit_of_forall_mem_span b hb hH := hS.isUnit_of_forall_mem_span b hb fun g hg => hH g (h hg)

/-- **Galois descent for admissibility, basis form**: for a ring `S` that is `(F, H')`-regular
and a finite-dimensional `V`, `S ⊗_F V` has an `S`-basis of `H`-fixed vectors if and only if it
has an `S`-basis of `H'`-fixed vectors, for `H' ≤ H` normal in `H` and of finite index such that
`H/H'` acts faithfully on `S^{H'}` (every `h ∈ H` fixing `S^{H'}` pointwise lies in `H'`). -/
theorem IsRegularPeriodRing.hasFixedBasis_iff_of_normal (hS : IsRegularPeriodRing act H')
    (ρ : Representation F G V) [FiniteDimensional F V] (hle : H' ≤ H)
    (hN : (H'.subgroupOf H).Normal) [(H'.subgroupOf H).FiniteIndex]
    (hfaithful : ∀ h ∈ H, (∀ x ∈ fixedSubalgebra S act H', act h x = x) → h ∈ H') :
    ρ.HasFixedBasis act H ↔ ρ.HasFixedBasis act H' := by
  rw [← (hS.mono hle).isAdmissible_iff_hasFixedBasis ρ, ← hS.isAdmissible_iff_hasFixedBasis ρ,
    isAdmissible_iff_of_normal ρ hle hN hS.isField hfaithful]

/-- **Galois descent for admissibility, comparison form**: for a ring `S` that is
`(F, H')`-regular and a finite-dimensional `V`, the comparison map
`α_V : S ⊗_{S^H} D_{S,H}(V) → S ⊗_F V` is an isomorphism if and only if
`α_V : S ⊗_{S^{H'}} D_{S,H'}(V) → S ⊗_F V` is, for `H' ≤ H` normal in `H` and of finite index
such that `H/H'` acts faithfully on `S^{H'}` (every `h ∈ H` fixing `S^{H'}` pointwise lies in
`H'`). -/
theorem IsRegularPeriodRing.comparison_bijective_iff_of_normal (hS : IsRegularPeriodRing act H')
    (ρ : Representation F G V) [FiniteDimensional F V] (hle : H' ≤ H)
    (hN : (H'.subgroupOf H).Normal) [(H'.subgroupOf H).FiniteIndex]
    (hfaithful : ∀ h ∈ H, (∀ x ∈ fixedSubalgebra S act H', act h x = x) → h ∈ H') :
    Function.Bijective (ρ.comparison act H) ↔ Function.Bijective (ρ.comparison act H') := by
  rw [← (hS.mono hle).isAdmissible_iff_comparison_bijective ρ,
    ← hS.isAdmissible_iff_comparison_bijective ρ,
    isAdmissible_iff_of_normal ρ hle hN hS.isField hfaithful]

end Regular

end Descent

end Representation
