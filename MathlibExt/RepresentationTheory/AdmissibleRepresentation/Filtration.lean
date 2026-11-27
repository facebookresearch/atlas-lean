/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Data.Int.Interval
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.RingTheory.TensorProduct.Free
public import MathlibExt.RepresentationTheory.AdmissibleRepresentation.Regular

/-!
# Filtered rings of periods

Let `F` be a field, `G` a group acting on a commutative `F`-algebra `S` through a family
`act : G → (S →ₐ[F] S)` of `F`-algebra maps, `H` a subgroup of `G`, `E = S^H` the ring of
invariants and `ρ` a representation of `G` on an `F`-vector space `V`, with
`D_S(V) = (S ⊗_F V)^H` (`Representation.periods`). Let `(Fil^i S)_{i ∈ ℤ}` be a family of
`F`-subspaces of `S` stable under multiplication by `E`, such as the filtration of Fontaine's field
`B_dR`. Following J.-M. Fontaine, *Représentations p-adiques semi-stables*, Astérisque 223 (1994),
Exposé III, §3.4 p. 140 and §3.7 pp. 141–142, we define

* `Fil^i D_S(V) = (Fil^i S ⊗_F V)^H` (`Representation.periodsFiltration`): the elements of
  `D_S(V)` lying in the image of `Fil^i S ⊗_F V` in `S ⊗_F V`, an `E`-submodule;
* `gr^i D_S(V) = Fil^i D_S(V) / Fil^{i+1} D_S(V)` (`Representation.periodsGraded`), an
  `E`-module, with the quotient map `Representation.periodsGradedMk` and the maps
  `Representation.periodsGradedLift` induced by maps on `Fil^i D_S(V)` vanishing on
  `Fil^{i+1} D_S(V)`.

## Main results

For a decreasing filtration (`Antitone`) that is exhaustive (`⋃ᵢ Fil^i S = S`) and separated
(`⋂ᵢ Fil^i S = 0`), a regular ring `S` (`Representation.IsRegularPeriodRing`, so that `E` is a
field) with `E` finite-dimensional over `F`, and a finite-dimensional `V`:

* the filtration of `D_S(V)` is finite: `Fil^i D_S(V) = D_S(V)` for `i` small enough
  (`Representation.exists_periodsFiltration_eq_periods`) and `Fil^i D_S(V) = 0` for `i` large
  enough (`Representation.exists_periodsFiltration_eq_bot`);
* `dim_E D_S(V) = Σᵢ dim_E gr^i D_S(V)`
  (`Representation.finrank_periods_eq_finsum_finrank_periodsGraded`), the sum having finite
  support (`Representation.finite_support_finrank_periodsGraded`).

As in `MathlibExt.RepresentationTheory.AdmissibleRepresentation`, the actions are abstract group
actions: no topology is involved.

## Implementation notes

The graded pieces are quotients of submodules of `S ⊗_F V` over `S^H`; synthesizing their
instances requires `maxSynthPendingDepth 2`, set on the declarations that need it. Dimension
counts go through `F`, whose field structure is an instance, and `[S^H : F]`.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Representation

variable {F G S V : Type*} [Field F] [Group G] [CommRing S] [Algebra F S] [AddCommGroup V]
  [Module F V]

/-! ### `Fil^i S ⊗ V` inside `S ⊗ V` -/

section Tensor

variable (act : G → S →ₐ[F] S) (H : Subgroup G)

/-- If an `F`-subspace `W` of `S` is stable under multiplication by `S^H`, then so is the image of
`W ⊗_F V` in `S ⊗_F V`. -/
theorem smul_mem_range_rTensor {W : Submodule F S}
    (hW : ∀ c ∈ fixedSubalgebra S act H, ∀ x ∈ W, c * x ∈ W) (c : fixedSubalgebra S act H)
    {z : S ⊗[F] V} (hz : z ∈ LinearMap.range (LinearMap.rTensor V W.subtype)) :
    c • z ∈ LinearMap.range (LinearMap.rTensor V W.subtype) := by
  obtain ⟨y, rfl⟩ := hz
  induction y using TensorProduct.inductionOn with
  | tmul w v =>
    refine ⟨⟨(c : S) * w, hW c c.2 w w.2⟩ ⊗ₜ v, ?_⟩
    rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul]
    exact (TensorProduct.smul_tmul' c (w : S) v).symm
  | add x y hx hy => rw [map_add, smul_add]; exact add_mem hx hy

/-- **Exhaustiveness passes to `S ⊗ V`**: if `(Fil^i S)` is decreasing and exhaustive, every
element of `S ⊗_F V` lies in the image of some `Fil^i S ⊗_F V`. -/
theorem exists_mem_range_rTensor {fil : ℤ → Submodule F S} (hanti : Antitone fil)
    (hexh : ∀ s : S, ∃ i, s ∈ fil i) (z : S ⊗[F] V) :
    ∃ i, z ∈ LinearMap.range (LinearMap.rTensor V (fil i).subtype) := by
  have hmono {i j : ℤ} (h : i ≤ j) :
      LinearMap.range (LinearMap.rTensor V (fil j).subtype) ≤
        LinearMap.range (LinearMap.rTensor V (fil i).subtype) := by
    rintro _ ⟨y, rfl⟩
    refine ⟨LinearMap.rTensor V (Submodule.inclusion (hanti h)) y, ?_⟩
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, Submodule.subtype_comp_inclusion]
  induction z using TensorProduct.inductionOn with
  | tmul s v =>
    obtain ⟨i, hi⟩ := hexh s
    exact ⟨i, ⟨(⟨s, hi⟩ : fil i) ⊗ₜ v, rfl⟩⟩
  | add x y hx hy =>
    obtain ⟨i, hi⟩ := hx
    obtain ⟨j, hj⟩ := hy
    exact ⟨min i j, add_mem (hmono (min_le_left i j) hi) (hmono (min_le_right i j) hj)⟩

/-- The coordinates of an element of the image of `W ⊗_F V` in `S ⊗_F V`, in the `S`-basis
`(1 ⊗ bₖ)` given by a basis `b` of `V`, lie in `W`. -/
theorem repr_mem_of_mem_range_rTensor {ι : Type*} (W : Submodule F S) (b : Module.Basis ι F V)
    {z : S ⊗[F] V} (hz : z ∈ LinearMap.range (LinearMap.rTensor V W.subtype)) (k : ι) :
    (Algebra.TensorProduct.basis S b).repr z k ∈ W := by
  obtain ⟨y, rfl⟩ := hz
  induction y using TensorProduct.inductionOn with
  | tmul w v =>
    rw [LinearMap.rTensor_tmul, Submodule.subtype_apply, Algebra.TensorProduct.basis_repr_tmul,
      Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, mul_comm, ← Algebra.smul_def]
    exact W.smul_mem _ w.2
  | add x y hx hy =>
    rw [map_add, map_add, Finsupp.add_apply]
    exact W.add_mem hx hy

/-- **Separatedness passes to `S ⊗ V`**: if `⋂ᵢ Fil^i S = 0`, an element of `S ⊗_F V` lying in the
image of every `Fil^i S ⊗_F V` is `0`, since its coordinates in a basis `(1 ⊗ bₖ)` lie in every
`Fil^i S`. -/
theorem eq_zero_of_forall_mem_range_rTensor {fil : ℤ → Submodule F S}
    (hsep : ∀ s : S, (∀ i, s ∈ fil i) → s = 0) {z : S ⊗[F] V}
    (hz : ∀ i, z ∈ LinearMap.range (LinearMap.rTensor V (fil i).subtype)) : z = 0 := by
  let b := Module.Free.chooseBasis F V
  refine (Algebra.TensorProduct.basis S b).repr.injective (Finsupp.ext fun k => ?_)
  rw [map_zero, Finsupp.zero_apply]
  exact hsep _ fun i => repr_mem_of_mem_range_rTensor (fil i) b (hz i) k

end Tensor

/-! ### The filtration of `D_S(V)` and its graded pieces -/

section Filtration

variable (ρ : Representation F G V) (act : G → S →ₐ[F] S) (H : Subgroup G)
  (fil : ℤ → Submodule F S) (hfil : ∀ i, ∀ c ∈ fixedSubalgebra S act H, ∀ x ∈ fil i, c * x ∈ fil i)

/-- **The filtration of `D_S(V)`** (J.-M. Fontaine, *Représentations p-adiques semi-stables*,
Astérisque 223 (1994), Exposé III, §3.7 p. 141, for `S = B_dR`): for a family `(Fil^i S)_{i ∈ ℤ}`
of `F`-subspaces of `S` stable under multiplication by `S^H`,
`Fil^i D_S(V) = (Fil^i S ⊗_F V)^H` is the `S^H`-submodule of `S ⊗_F V` of the elements of
`D_S(V) = (S ⊗_F V)^H` lying in the image of `Fil^i S ⊗_F V`. -/
def periodsFiltration (i : ℤ) : Submodule (fixedSubalgebra S act H) (S ⊗[F] V) where
  carrier := {x | x ∈ ρ.periods act H ∧ x ∈ LinearMap.range (LinearMap.rTensor V (fil i).subtype)}
  add_mem' hx hy := ⟨add_mem hx.1 hy.1, add_mem hx.2 hy.2⟩
  zero_mem' := ⟨zero_mem _, zero_mem _⟩
  smul_mem' c _ hx := ⟨Submodule.smul_mem _ c hx.1, smul_mem_range_rTensor act H (hfil i) c hx.2⟩

/-- `x ∈ Fil^i D_S(V)` if and only if `x ∈ D_S(V)` and `x` lies in the image of
`Fil^i S ⊗_F V`. -/
theorem mem_periodsFiltration {i : ℤ} {x : S ⊗[F] V} :
    x ∈ ρ.periodsFiltration act H fil hfil i ↔
      x ∈ ρ.periods act H ∧ x ∈ LinearMap.range (LinearMap.rTensor V (fil i).subtype) :=
  Iff.rfl

/-- `Fil^i D_S(V) ⊆ D_S(V)`. -/
theorem periodsFiltration_le_periods (i : ℤ) :
    ρ.periodsFiltration act H fil hfil i ≤ ρ.periods act H :=
  fun _ hx => hx.1

/-- **The filtration of `D_S(V)` is decreasing** if the filtration of `S` is. -/
theorem periodsFiltration_antitone (hanti : Antitone fil) :
    Antitone (ρ.periodsFiltration act H fil hfil) := by
  intro i j hij x hx
  obtain ⟨y, hy⟩ := hx.2
  refine ⟨hx.1, LinearMap.rTensor V (Submodule.inclusion (hanti hij)) y, ?_⟩
  rw [← hy, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp, Submodule.subtype_comp_inclusion]

set_option maxSynthPendingDepth 2 in
/-- **The graded piece `gr^i D_S(V) = Fil^i D_S(V) / Fil^{i+1} D_S(V)`**, an `S^H`-module. -/
def periodsGraded (i : ℤ) : Type _ :=
  ρ.periodsFiltration act H fil hfil i ⧸
    (ρ.periodsFiltration act H fil hfil (i + 1)).comap
      (ρ.periodsFiltration act H fil hfil i).subtype

set_option maxSynthPendingDepth 2 in
/-- The additive group `gr^i D_S(V)`. -/
instance instAddCommGroupPeriodsGraded (i : ℤ) :
    AddCommGroup (ρ.periodsGraded act H fil hfil i) :=
  Submodule.Quotient.addCommGroup _

set_option maxSynthPendingDepth 2 in
/-- `gr^i D_S(V)` is a module over `S^H`. -/
instance instModulePeriodsGraded (i : ℤ) :
    Module (fixedSubalgebra S act H) (ρ.periodsGraded act H fil hfil i) :=
  Submodule.Quotient.module _

set_option maxSynthPendingDepth 2 in
/-- `gr^i D_S(V)` is an `F`-vector space. -/
instance instModuleFieldPeriodsGraded (i : ℤ) : Module F (ρ.periodsGraded act H fil hfil i) :=
  Submodule.Quotient.module' _

set_option maxSynthPendingDepth 2 in
/-- The scalars `F ⊆ S^H` act compatibly on `gr^i D_S(V)`. -/
instance instIsScalarTowerPeriodsGraded (i : ℤ) :
    IsScalarTower F (fixedSubalgebra S act H) (ρ.periodsGraded act H fil hfil i) :=
  Submodule.Quotient.isScalarTower _ _

set_option maxSynthPendingDepth 2 in
/-- **The quotient map `Fil^i D_S(V) → gr^i D_S(V)`**, an `S^H`-linear surjection. -/
def periodsGradedMk (i : ℤ) :
    ρ.periodsFiltration act H fil hfil i →ₗ[fixedSubalgebra S act H]
      ρ.periodsGraded act H fil hfil i :=
  Submodule.mkQ _

set_option maxSynthPendingDepth 2 in
/-- The quotient map `Fil^i D_S(V) → gr^i D_S(V)` is surjective. -/
theorem periodsGradedMk_surjective (i : ℤ) :
    Function.Surjective (ρ.periodsGradedMk act H fil hfil i) :=
  Submodule.mkQ_surjective _

set_option maxSynthPendingDepth 2 in
/-- The class of `x ∈ Fil^i D_S(V)` in `gr^i D_S(V)` vanishes if and only if
`x ∈ Fil^{i+1} D_S(V)`. -/
theorem periodsGradedMk_eq_zero_iff {i : ℤ} (x : ρ.periodsFiltration act H fil hfil i) :
    ρ.periodsGradedMk act H fil hfil i x = 0 ↔
      (x : S ⊗[F] V) ∈ ρ.periodsFiltration act H fil hfil (i + 1) :=
  Submodule.Quotient.mk_eq_zero _

set_option maxSynthPendingDepth 2 in
/-- **The map `gr^i D_S(V) → W` induced by an `F`-linear map `f : Fil^i D_S(V) → W` vanishing on
`Fil^{i+1} D_S(V)`.** -/
def periodsGradedLift {W : Type*} [AddCommGroup W] [Module F W] {i : ℤ}
    (f : ρ.periodsFiltration act H fil hfil i →ₗ[F] W)
    (hf : ∀ x : ρ.periodsFiltration act H fil hfil i,
      (x : S ⊗[F] V) ∈ ρ.periodsFiltration act H fil hfil (i + 1) → f x = 0) :
    ρ.periodsGraded act H fil hfil i →ₗ[F] W :=
  (((ρ.periodsFiltration act H fil hfil (i + 1)).comap
      (ρ.periodsFiltration act H fil hfil i).subtype).restrictScalars F).liftQ f
      (fun x hx => LinearMap.mem_ker.2 (hf x hx)) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv F _).symm.toLinearMap

set_option maxSynthPendingDepth 2 in
variable {ρ act H fil hfil} in
/-- The map induced by `f` sends the class of `x` to `f x`. -/
@[simp]
theorem periodsGradedLift_periodsGradedMk {W : Type*} [AddCommGroup W] [Module F W] {i : ℤ}
    (f : ρ.periodsFiltration act H fil hfil i →ₗ[F] W)
    (hf : ∀ x : ρ.periodsFiltration act H fil hfil i,
      (x : S ⊗[F] V) ∈ ρ.periodsFiltration act H fil hfil (i + 1) → f x = 0)
    (x : ρ.periodsFiltration act H fil hfil i) :
    ρ.periodsGradedLift act H fil hfil f hf (ρ.periodsGradedMk act H fil hfil i x) = f x :=
  rfl

set_option maxSynthPendingDepth 2 in
variable {ρ act H fil hfil} in
/-- The map induced by `f` is injective if the kernel of `f` is `Fil^{i+1} D_S(V)`. -/
theorem periodsGradedLift_injective {W : Type*} [AddCommGroup W] [Module F W] {i : ℤ}
    (f : ρ.periodsFiltration act H fil hfil i →ₗ[F] W)
    (hf : ∀ x : ρ.periodsFiltration act H fil hfil i,
      (x : S ⊗[F] V) ∈ ρ.periodsFiltration act H fil hfil (i + 1) → f x = 0)
    (hf' : ∀ x : ρ.periodsFiltration act H fil hfil i,
      f x = 0 → (x : S ⊗[F] V) ∈ ρ.periodsFiltration act H fil hfil (i + 1)) :
    Function.Injective (ρ.periodsGradedLift act H fil hfil f hf) := by
  refine (injective_iff_map_eq_zero _).2 fun q hq => ?_
  obtain ⟨x, rfl⟩ := ρ.periodsGradedMk_surjective act H fil hfil i q
  rw [periodsGradedLift_periodsGradedMk] at hq
  exact (ρ.periodsGradedMk_eq_zero_iff act H fil hfil x).2 (hf' x hq)

end Filtration

/-! ### Finiteness of the filtration and dimensions -/

section Dimension

/-- Telescoping for `ℕ`-valued sequences: if `g i + f (i + 1) = f i` for all `i`, `f` is constant
below `a` and vanishes from `b` on, then `g` is supported in `[a, b)` and `Σᵢ g i = f a`. -/
private theorem finsum_eq_of_add_eq {f g : ℤ → ℕ} {a b : ℤ} (hfg : ∀ i, g i + f (i + 1) = f i)
    (ha : ∀ i ≤ a, f i = f a) (hb : ∀ i, b ≤ i → f i = 0) :
    Function.support g ⊆ Set.Ico a b ∧ ∑ᶠ i, g i = f a := by
  have hsupp : Function.support g ⊆ Set.Ico a b := by
    intro i hi
    rw [Function.mem_support] at hi
    rw [Set.mem_Ico]
    by_contra hcon
    apply hi
    have h := hfg i
    rcases not_and_or.mp hcon with h' | h'
    · rw [ha i (by omega), ha (i + 1) (by omega)] at h
      omega
    · rw [hb i (by omega), hb (i + 1) (by omega)] at h
      omega
  refine ⟨hsupp, ?_⟩
  rw [finsum_eq_sum_of_support_subset g (s := Finset.Ico a b) (by rwa [Finset.coe_Ico])]
  have key (m : ℕ) : ∑ i ∈ Finset.Ico a (a + m), g i + f (a + m) = f a := by
    induction m with
    | zero => simp
    | succ m ih =>
      have hI : Finset.Ico a (a + ((m + 1 : ℕ) : ℤ)) = insert (a + m) (Finset.Ico a (a + m)) := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_Ico]
        omega
      have hnot : a + (m : ℤ) ∉ Finset.Ico a (a + m) := by simp
      have h := hfg (a + m)
      rw [hI, Finset.sum_insert hnot, show a + ((m + 1 : ℕ) : ℤ) = a + m + 1 by omega]
      omega
  rcases le_or_gt a b with hab | hab
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, b = a + n := ⟨(b - a).toNat, by omega⟩
    have h := key n
    rw [hb (a + n) le_rfl, add_zero] at h
    exact h
  · rw [Finset.Ico_eq_empty_of_le hab.le, Finset.sum_empty, hb a hab.le]

variable [IsDomain S] {act : G →* (S →ₐ[F] S)} {H : Subgroup G} (hS : IsRegularPeriodRing act H)
  (ρ : Representation F G V) {fil : ℤ → Submodule F S}
  (hfil : ∀ i, ∀ c ∈ fixedSubalgebra S act H, ∀ x ∈ fil i, c * x ∈ fil i)

include hS

/-- For a regular ring `S`, a nonzero element of `D_S(V)` gives `dim_{S^H} D_S(V) ≥ 1`. -/
theorem one_le_finrank_periods [FiniteDimensional F V] {x : S ⊗[F] V} (hx : x ∈ ρ.periods act H)
    (hx0 : x ≠ 0) : 1 ≤ Module.finrank (fixedSubalgebra S act H) (ρ.periods act H) := by
  have := hS.finite_periods ρ
  have := hS.free_periods ρ
  have : Nontrivial (ρ.periods act H) :=
    ⟨⟨⟨x, hx⟩, 0, fun h => hx0 (congrArg Subtype.val h)⟩⟩
  exact Module.finrank_pos (R := fixedSubalgebra S act H) (M := ρ.periods act H)

/-- **The filtration of `D_S(V)` is exhaustive** (Fontaine, *Représentations p-adiques
semi-stables*, Exposé III, §3.7 p. 141): for a decreasing exhaustive filtration of a regular ring
`S` and a finite-dimensional `V`, `Fil^i D_S(V) = D_S(V)` for `i` small enough, since `D_S(V)` is
finitely generated over `S^H`. -/
theorem exists_periodsFiltration_eq_periods [FiniteDimensional F V] (hanti : Antitone fil)
    (hexh : ∀ s : S, ∃ i, s ∈ fil i) :
    ∃ a, ∀ i ≤ a, ρ.periodsFiltration act H fil hfil i = ρ.periods act H := by
  have := hS.finite_periods ρ
  obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := fixedSubalgebra S act H) (M := ρ.periods act H)
  choose n hn using fun x : ρ.periods act H => exists_mem_range_rTensor hanti hexh (x : S ⊗[F] V)
  obtain ⟨a, ha⟩ := (t.image n).bddBelow
  refine ⟨a, fun i hi => le_antisymm (ρ.periodsFiltration_le_periods act H fil hfil i) ?_⟩
  refine le_trans ?_ (ρ.periodsFiltration_antitone act H fil hfil hanti hi)
  rw [← Submodule.map_subtype_top (ρ.periods act H), ← ht, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨x.2, ?_⟩
  obtain ⟨y, hy⟩ := hn x
  refine ⟨LinearMap.rTensor V
    (Submodule.inclusion (hanti (ha (Finset.mem_coe.2 (Finset.mem_image_of_mem n hx))))) y, ?_⟩
  rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, Submodule.subtype_comp_inclusion]
  exact hy

/-- `Fil^i D_S(V)` is finite-dimensional over `F` when `S^H` is. -/
theorem finiteDimensional_periodsFiltration [FiniteDimensional F V]
    [Module.Finite F (fixedSubalgebra S act H)] (i : ℤ) :
    FiniteDimensional F ((ρ.periodsFiltration act H fil hfil i).restrictScalars F) := by
  have := hS.finite_periods ρ
  have : Module.Finite (fixedSubalgebra S act H) ((ρ.periods act H).restrictScalars F) := this
  have : FiniteDimensional F ((ρ.periods act H).restrictScalars F) :=
    Module.Finite.trans (fixedSubalgebra S act H) _
  exact Submodule.finiteDimensional_of_le (S₂ := (ρ.periods act H).restrictScalars F)
    fun _ hx => ρ.periodsFiltration_le_periods act H fil hfil i hx

/-- **The filtration of `D_S(V)` is separated**: for a decreasing separated filtration of a regular
ring `S` with `S^H` finite over `F` and a finite-dimensional `V`, `Fil^i D_S(V) = 0` for `i` large
enough: the chain `(Fil^n D_S(V))_{n ∈ ℕ}` of subspaces of the finite-dimensional `F`-vector space
`D_S(V)` stabilizes, and an element of the stable term lies in every `Fil^i S ⊗ V`. -/
theorem exists_periodsFiltration_eq_bot [FiniteDimensional F V]
    [Module.Finite F (fixedSubalgebra S act H)] (hanti : Antitone fil)
    (hsep : ∀ s : S, (∀ i, s ∈ fil i) → s = 0) :
    ∃ b, ∀ i, b ≤ i → ρ.periodsFiltration act H fil hfil i = ⊥ := by
  classical
  have hfd := ρ.finiteDimensional_periodsFiltration hS hfil
  let d : ℕ → ℕ := fun n =>
    Module.finrank F ((ρ.periodsFiltration act H fil hfil n).restrictScalars F)
  have hex : ∃ k, ∃ n, d n = k := ⟨d 0, 0, rfl⟩
  obtain ⟨n₀, hn₀⟩ := Nat.find_spec hex
  have hstab (n : ℕ) (hn : n₀ ≤ n) :
      ρ.periodsFiltration act H fil hfil n = ρ.periodsFiltration act H fil hfil n₀ := by
    have := hfd n₀
    have hle : (ρ.periodsFiltration act H fil hfil n).restrictScalars F ≤
        (ρ.periodsFiltration act H fil hfil n₀).restrictScalars F :=
      ρ.periodsFiltration_antitone act H fil hfil hanti (by exact_mod_cast hn)
    have hdle : d n ≤ d n₀ := Submodule.finrank_mono hle
    have hdge : Nat.find hex ≤ d n := Nat.find_min' hex ⟨n, rfl⟩
    refine Submodule.restrictScalars_injective F _ _ (Submodule.eq_of_le_of_finrank_eq hle ?_)
    change d n = d n₀
    omega
  refine ⟨n₀, fun i hi => eq_bot_iff.2 fun x hx => ?_⟩
  have hx₀ : x ∈ ρ.periodsFiltration act H fil hfil n₀ :=
    ρ.periodsFiltration_antitone act H fil hfil hanti hi hx
  refine (Submodule.mem_bot _).2 (eq_zero_of_forall_mem_range_rTensor hsep fun j => ?_)
  rcases le_total j n₀ with hj | hj
  · exact (ρ.periodsFiltration_antitone act H fil hfil hanti hj hx₀).2
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, j = m := ⟨j.toNat, by omega⟩
    rw [← hstab m (by exact_mod_cast hj)] at hx₀
    exact hx₀.2

set_option maxSynthPendingDepth 2 in
/-- `dim_F gr^i D_S(V) + dim_F Fil^{i+1} D_S(V) = dim_F Fil^i D_S(V)`. -/
private theorem finrank_periodsGraded_add_finrank [FiniteDimensional F V]
    [Module.Finite F (fixedSubalgebra S act H)] (hanti : Antitone fil) (i : ℤ) :
    Module.finrank F (ρ.periodsGraded act H fil hfil i) +
        Module.finrank F (ρ.periodsFiltration act H fil hfil (i + 1)) =
      Module.finrank F (ρ.periodsFiltration act H fil hfil i) := by
  have hle := ρ.periodsFiltration_antitone act H fil hfil hanti (show i ≤ i + 1 by omega)
  have : FiniteDimensional F (ρ.periodsFiltration act H fil hfil i) :=
    ρ.finiteDimensional_periodsFiltration hS hfil i
  let N := (ρ.periodsFiltration act H fil hfil (i + 1)).comap
    (ρ.periodsFiltration act H fil hfil i).subtype
  have h₁ := Submodule.finrank_quotient_add_finrank (R := F)
    (M := ρ.periodsFiltration act H fil hfil i) (N.restrictScalars F)
  have h₂ : Module.finrank F (ρ.periodsFiltration act H fil hfil i ⧸ N.restrictScalars F) =
      Module.finrank F (ρ.periodsGraded act H fil hfil i) :=
    (Submodule.Quotient.restrictScalarsEquiv (M := ρ.periodsFiltration act H fil hfil i) F
      N).finrank_eq
  let e : N.restrictScalars F ≃ₗ[F] ρ.periodsFiltration act H fil hfil (i + 1) :=
    { toFun := fun y => ⟨y.1.1, y.2⟩
      invFun := fun z => ⟨⟨z.1, hle z.2⟩, z.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← h₂, ← e.finrank_eq]
  exact h₁

/-- `dim_F D_S(V) = Σᵢ dim_F gr^i D_S(V)`, the sum having finite support. -/
private theorem finrank_periods_eq_finsum_aux [FiniteDimensional F V]
    [Module.Finite F (fixedSubalgebra S act H)] (hanti : Antitone fil)
    (hexh : ∀ s : S, ∃ i, s ∈ fil i) (hsep : ∀ s : S, (∀ i, s ∈ fil i) → s = 0) :
    (Function.support fun i => Module.finrank F (ρ.periodsGraded act H fil hfil i)).Finite ∧
      ∑ᶠ i, Module.finrank F (ρ.periodsGraded act H fil hfil i) =
        Module.finrank F (ρ.periods act H) := by
  obtain ⟨a, ha⟩ := ρ.exists_periodsFiltration_eq_periods hS hfil hanti hexh
  obtain ⟨b, hb⟩ := ρ.exists_periodsFiltration_eq_bot hS hfil hanti hsep
  obtain ⟨hsupp, hsum⟩ := finsum_eq_of_add_eq
    (f := fun i => Module.finrank F (ρ.periodsFiltration act H fil hfil i)) (a := a) (b := b)
    (ρ.finrank_periodsGraded_add_finrank hS hfil hanti)
    (fun i hi => by rw [ha i hi, ha a le_rfl])
    (fun i hi => by
      rw [hb i hi]
      exact Module.finrank_zero_of_subsingleton)
  refine ⟨(Set.finite_Ico a b).subset hsupp, ?_⟩
  rw [hsum, ha a le_rfl]

/-- `dim_F gr^i D_S(V) = [S^H : F] · dim_{S^H} gr^i D_S(V)`. -/
theorem finrank_mul_finrank_periodsGraded [Module.Finite F (fixedSubalgebra S act H)] (i : ℤ) :
    Module.finrank F (fixedSubalgebra S act H) *
        Module.finrank (fixedSubalgebra S act H) (ρ.periodsGraded act H fil hfil i) =
      Module.finrank F (ρ.periodsGraded act H fil hfil i) := by
  have : Module.Free (fixedSubalgebra S act H) (ρ.periodsGraded act H fil hfil i) := by
    let := hS.field
    exact Module.Free.of_divisionRing _ _
  exact Module.finrank_mul_finrank F (fixedSubalgebra S act H) _

/-- **The graded pieces `gr^i D_S(V)` vanish for all but finitely many `i`.** -/
theorem finite_support_finrank_periodsGraded [FiniteDimensional F V]
    [Module.Finite F (fixedSubalgebra S act H)] (hanti : Antitone fil)
    (hexh : ∀ s : S, ∃ i, s ∈ fil i) (hsep : ∀ s : S, (∀ i, s ∈ fil i) → s = 0) :
    (Function.support fun i =>
      Module.finrank (fixedSubalgebra S act H) (ρ.periodsGraded act H fil hfil i)).Finite := by
  refine (ρ.finrank_periods_eq_finsum_aux hS hfil hanti hexh hsep).1.subset fun i hi => ?_
  rw [Function.mem_support, ← ρ.finrank_mul_finrank_periodsGraded hS hfil i]
  exact mul_ne_zero Module.finrank_pos.ne' hi

/-- **`dim_{S^H} D_S(V) = Σᵢ dim_{S^H} gr^i D_S(V)`** (Fontaine, *Représentations p-adiques
semi-stables*, Exposé III, §3.7 p. 142, for `S = B_dR`): for a decreasing, exhaustive and
separated filtration of a regular ring `S` with `S^H` finite over `F`, and a finite-dimensional
`V`, the filtration of `D_S(V)` is finite and the dimension of `D_S(V)` is the sum of the dimensions
of its graded pieces. -/
theorem finrank_periods_eq_finsum_finrank_periodsGraded [FiniteDimensional F V]
    [Module.Finite F (fixedSubalgebra S act H)] (hanti : Antitone fil)
    (hexh : ∀ s : S, ∃ i, s ∈ fil i) (hsep : ∀ s : S, (∀ i, s ∈ fil i) → s = 0) :
    Module.finrank (fixedSubalgebra S act H) (ρ.periods act H) =
      ∑ᶠ i, Module.finrank (fixedSubalgebra S act H) (ρ.periodsGraded act H fil hfil i) := by
  have := hS.free_periods ρ
  have hpos : 0 < Module.finrank F (fixedSubalgebra S act H) := Module.finrank_pos
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  rw [Module.finrank_mul_finrank F (fixedSubalgebra S act H),
    ← (ρ.finrank_periods_eq_finsum_aux hS hfil hanti hexh hsep).2,
    mul_finsum _ _]
  exact finsum_congr fun i => (ρ.finrank_mul_finrank_periodsGraded hS hfil i).symm

end Dimension

end Representation
