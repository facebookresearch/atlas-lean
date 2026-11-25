/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Module.CharacterModule
import Mathlib.Topology.Instances.AddCircle.Real
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Algebra.Group.GroupTopology

/-!
# Absolutely dense partitions of countable abelian groups

We prove the positive answer to Kourovka Problem 13.47. In a compact group containing the
given group, we successively color pairs reflected about each of its elements. At each stage,
a pair is recorded by giving its two points the same coordinate and opposite bits. Rounding
the coordinates near finitely many possible values lets us fold a new neighborhood about
its center while preserving earlier pairs. An ultrafilter limit gives a single coloring.

For any non-discrete Hausdorff group topology, every identity neighborhood is infinite.
Compactness gives two points there whose images are arbitrarily close, and finite 2-torsion
lets us choose their difference distinct from its negative. Translating this difference and
its negative gives both colors in any prescribed neighborhood.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.AbsolutelyDensePartitionKourovka13Problem47Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 13.47 (I. V.
Protasov). UnsolvedMath record UM-00700965 (`KOU-13.47`), dataset ulamai/UnsolvedMath v1.8.0.

"Every group topology" is read as every non-discrete Hausdorff group topology: no proper subset is
dense in the discrete topology, and without the Hausdorff condition the claim fails, e.g. for `ℤ ×
(ℤ/3)²` (the topology whose open sets are unions of cosets of a subgroup of order `3` forces every
line of the affine plane over `𝔽₃` to meet both cells, and that plane has no such 2-colouring). This
is Protasov's notion of an absolutely dense subset. Topologies range over Mathlib's `GroupTopology
G`.
-/

/-- **Protasov's question on absolutely dense partitions (Kourovka 13.47).** The proposition that
every countable abelian group $G$ with only finitely many elements of order $2$ can be partitioned
into two disjoint sets $A_1$ and $A_2$ with $A_1 \cup A_2 = G$ such that $A_1$ and $A_2$ are both
dense in every non-discrete Hausdorff group topology on $G$. -/
def countableAbsolutelyDensePartition : Prop :=
  ∀ (G : Type) [CommGroup G], Countable G → {g : G | g ≠ 1 ∧ g ^ 2 = 1}.Finite →
    ∃ A₁ A₂ : Set G, A₁ ∪ A₂ = Set.univ ∧ Disjoint A₁ A₂ ∧
      ∀ τ : GroupTopology G, @T2Space G τ.toTopologicalSpace → τ.toTopologicalSpace ≠ ⊥ →
        @Dense G τ.toTopologicalSpace A₁ ∧ @Dense G τ.toTopologicalSpace A₂

open Set Filter
open scoped Topology

private noncomputable def ratCircleHom : AddCircle (1 : ℚ) →+ UnitAddCircle :=
  QuotientAddGroup.map _ _ (Rat.castHom ℝ).toAddMonoidHom <| by
    rw [AddSubgroup.zmultiples_le]
    change ((1 : ℚ) : ℝ) ∈ AddSubgroup.zmultiples (1 : ℝ)
    simp

private theorem ratCircleHom_injective : Function.Injective ratCircleHom := by
  apply (injective_iff_map_eq_zero _).2
  intro x
  induction x using QuotientAddGroup.induction_on with
  | _ q =>
    change ((q : ℝ) : UnitAddCircle) = 0 → (q : AddCircle (1 : ℚ)) = 0
    rw [AddCircle.coe_eq_zero_iff, AddCircle.coe_eq_zero_iff]
    rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simp only [zsmul_one] at hn ⊢
    exact_mod_cast hn

private abbrev Torus (G : Type*) [AddCommGroup G] := CharacterModule G → UnitAddCircle

private noncomputable def evaluation {G : Type*} [AddCommGroup G] : G →+ Torus G where
  toFun x χ := ratCircleHom (χ x)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

private lemma evaluation_injective {G : Type*} [AddCommGroup G] :
    Function.Injective (evaluation (G := G)) := by
  apply (injective_iff_map_eq_zero _).2
  intro x hx
  apply CharacterModule.eq_zero_of_character_apply
  intro χ
  apply ratCircleHom_injective
  simpa [evaluation] using congrFun hx χ

variable {K : Type*} [AddCommGroup K]

private def signed (b : Bool) (x : K) : K := if b then -x else x

private lemma signed_self (b : Bool) (x : K) : signed b (signed b x) = x := by
  cases b <;> simp [signed]

private lemma signed_sub (b : Bool) (x y : K) :
    signed b (x - y) = signed b x - signed b y := by
  cases b <;> simp [signed, sub_eq_add_neg, add_comm]

private lemma signed_xor (b c : Bool) (x : K) :
    signed (b ^^ c) x = signed c (signed b x) := by
  cases b <;> cases c <;> simp [signed]

/-- A finite set of possible origins, with a choice of orientation at each point. -/
private structure Chart (K : Type*) [AddCommGroup K] where
  origin : K → K
  finite_origin : (range origin).Finite
  bit : K → Bool

private def Chart.coord (s : Chart K) (x : K) := signed (s.bit x) (x - s.origin x)

private def Chart.Paired (s : Chart K) (x y : K) :=
  s.coord x = s.coord y ∧ s.bit x ≠ s.bit y


/-- Round to each of finitely many specified points on a neighborhood of that point. -/
private lemma exists_rounding [TopologicalSpace K] [T2Space K] (D : Set K) (hD : D.Finite) :
    ∃ r : K → K, (range r).Finite ∧ ∀ d ∈ D, ∀ᶠ x in 𝓝 d, r x = d := by
  classical
  obtain ⟨U, hU, hsep⟩ := hD.t2_separation
  let r (x : K) := if h : ∃ d ∈ D, x ∈ U d then h.choose else 0
  refine ⟨r, (hD.insert 0).subset ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    dsimp [r]
    split <;> rename_i h
    · exact Or.inr h.choose_spec.1
    · exact Or.inl rfl
  intro d hd
  filter_upwards [(hU d).2.mem_nhds (hU d).1] with x hx
  have h : ∃ e ∈ D, x ∈ U e := ⟨d, hd, hx⟩
  dsimp [r]
  rw [dite_eq_left h]
  by_contra hne
  exact Set.disjoint_left.mp (hsep h.choose_spec.1 hd hne) h.choose_spec.2 hx

/-- Recenter the coordinates, then fold each displacement together with its negative. -/
private def Chart.fold (s : Chart K) (r : K → K) (hr : (range r).Finite)
    (orient : K → Bool) : Chart K where
  origin x := s.origin x + signed (s.bit x) (r (s.coord x))
  finite_origin := by
    let f (p : K × Bool × K) := p.1 + signed p.2.1 p.2.2
    apply ((s.finite_origin.prod (finite_univ.prod hr)).image f).subset
    rintro _ ⟨x, rfl⟩
    exact ⟨(s.origin x, s.bit x, r (s.coord x)),
      ⟨mem_range_self _, mem_univ _, mem_range_self _⟩, rfl⟩
  bit x := s.bit x ^^ orient (s.coord x - r (s.coord x))

private lemma Chart.coord_fold (s : Chart K) (r : K → K) (hr : (range r).Finite)
    (orient : K → Bool) (x : K) :
    (s.fold r hr orient).coord x =
      signed (orient (s.coord x - r (s.coord x))) (s.coord x - r (s.coord x)) := by
  simp only [Chart.coord, Chart.fold, signed_xor, ← sub_sub, signed_sub, signed_self]

private lemma Chart.paired_fold (s : Chart K) (r : K → K) (hr : (range r).Finite)
    (orient : K → Bool) {x y : K} (h : s.Paired x y) : (s.fold r hr orient).Paired x y := by
  obtain ⟨he, hb⟩ := h
  constructor
  · simp only [Chart.coord_fold, he]
  · simpa only [Chart.fold, he, ne_eq, Bool.xor_left_inj] using hb

private lemma exists_orientation : ∃ o : K → Bool, ∀ x, x ≠ -x → o (-x) = !(o x) := by
  classical
  let := linearOrderOfSTO (WellOrderingRel (α := K))
  refine ⟨fun x ↦ decide (x < -x), fun x h ↦ ?_⟩
  cases lt_or_gt_of_ne h with
  | inl h => simp [h, h.not_gt]
  | inr h => simp [h, h.not_gt]

private lemma Chart.fold_at (s : Chart K) (r : K → K) (hr : (range r).Finite)
    (o : K → Bool) (ho : ∀ x, x ≠ -x → o (-x) = !(o x)) (g v : K)
    (hv : v ≠ -v) (h : r (s.coord (g + v)) = signed (s.bit (g + v)) (g - s.origin (g + v))) :
    (s.fold r hr o).coord (g + v) = signed (o v) v ∧ (s.fold r hr o).bit (g + v) = o v := by
  have diff : s.coord (g + v) - r (s.coord (g + v)) = signed (s.bit (g + v)) v := by
    rw [h, Chart.coord, ← signed_sub]
    congr 1
    abel
  have hb : (s.fold r hr o).bit (g + v) = o v := by
    change (s.bit (g + v) ^^ o (s.coord (g + v) - r (s.coord (g + v)))) = o v
    rw [diff]
    cases s.bit (g + v) <;> simp [signed, ho v hv]
  refine ⟨?_, hb⟩
  rw [Chart.coord, hb]
  congr 1
  change g + v - (s.origin _ + signed _ (r (s.coord _))) = v
  rw [h, signed_self]
  abel

variable [TopologicalSpace K] [IsTopologicalAddGroup K]

/-- One refinement preserves all earlier pairs and handles reflections about a new center. -/
private lemma Chart.refine_at [T2Space K] (s : Chart K) (g : K) :
    ∃ t : Chart K, (∀ x y, s.Paired x y → t.Paired x y) ∧
      ∀ᶠ v in 𝓝 0, v ≠ -v → t.Paired (g + v) (g + -v) := by
  classical
  let f (p : Bool × K) := signed p.1 (g - p.2)
  obtain ⟨r, hr, hround⟩ := exists_rounding _ ((finite_univ.prod s.finite_origin).image f)
  obtain ⟨o, ho⟩ := exists_orientation (K := K)
  refine ⟨s.fold r hr o, fun _ _ ↦ s.paired_fold r hr o, ?_⟩
  have near : ∀ᶠ v in 𝓝 0, ∀ b : Bool, ∀ d ∈ range s.origin,
      r (signed b (g + v - d)) = signed b (g - d) := by
    apply eventually_all.2
    intro b
    apply s.finite_origin.eventually_all.2
    intro d hd
    have h := hround (f (b, d)) ⟨(b, d), ⟨trivial, hd⟩, rfl⟩
    have ht : Tendsto (fun v : K ↦ signed b (g + v - d)) (𝓝 0) (𝓝 (f (b, d))) := by
      have hc : Continuous (fun v : K ↦ signed b (g + v - d)) := by
        cases b <;> simp only [signed, Bool.false_eq_true, ite_false, ite_true] <;> fun_prop
      simpa [f] using hc.continuousAt.tendsto (x := 0)
    exact ht.eventually h
  have hn := (show Tendsto (fun v : K ↦ -v) (𝓝 0) (𝓝 0) by
    simpa using (continuous_neg.continuousAt.tendsto (x := (0 : K)))).eventually near
  filter_upwards [near, hn] with v hp hm
  intro hv
  have hneg : -v ≠ - -v := by simpa using hv.symm
  have hp' := s.fold_at r hr o ho g v hv (hp _ _ (mem_range_self _))
  have hm' := s.fold_at r hr o ho g (-v) hneg (hm _ _ (mem_range_self _))
  constructor
  · rw [hp'.1, hm'.1, ho v hv]
    cases o v <;> simp [signed]
  · rw [hp'.2, hm'.2, ho v hv]
    cases o v <;> decide

/-- An ultrafilter limit of the successive colors respects every pair once it is formed. -/
private lemma color_centers [T2Space K] (g : ℕ → K) :
    ∃ c : K → Bool, ∀ n, ∀ᶠ v in 𝓝 0, v ≠ -v → c (g n + v) ≠ c (g n + -v) := by
  classical
  choose next hkeep hnew using fun (n : ℕ) (s : Chart K) ↦ s.refine_at (g n)
  let stages : ℕ → Chart K := Nat.rec
    ⟨fun _ ↦ 0, by simp, fun _ ↦ false⟩ next
  let F := Ultrafilter.of (atTop : Filter ℕ)
  let c (x : K) := decide (∀ᶠ n in (F : Filter ℕ), (stages n).bit x = true)
  have limit (x : K) : ∀ᶠ n in (F : Filter ℕ), (stages n).bit x = c x := by
    dsimp [c]
    by_cases h : ∀ᶠ n in (F : Filter ℕ), (stages n).bit x = true
    · simp [h]
    · simp only [h, decide_false]
      have hn := Ultrafilter.compl_mem_iff_notMem (f := F) |>.2 h
      filter_upwards [hn] with n hn
      simpa using hn
  refine ⟨c, fun n ↦ ?_⟩
  filter_upwards [hnew n (stages n)] with v hv
  intro hne
  let x := g n + v
  let y := g n + -v
  have persist (m : ℕ) (hm : n + 1 ≤ m) : (stages m).Paired x y := by
    induction m, hm using Nat.le_induction with
    | base => exact hv hne
    | succ k _ ih => exact hkeep k (stages k) x y ih
  have tail : ∀ᶠ m in (F : Filter ℕ), n + 1 ≤ m :=
    Ultrafilter.of_le _ (eventually_ge_atTop _)
  obtain ⟨m, hm, hx, hy⟩ := (tail.and ((limit x).and (limit y))).exists
  exact hx ▸ hy ▸ (persist m hm).2

/-- Differences of points of an infinite set enter every given compact-group neighborhood of
zero, even after excluding finitely many choices of the second point for each first point. -/
private lemma close_pair [CompactSpace K] {A : Type*} [Infinite A] (f : A → K)
    (bad : A → Set A) (hbad : ∀ a, (bad a).Finite) {V : Set K} (hV : V ∈ 𝓝 0) :
    ∃ a b, b ∉ bad a ∧ f b - f a ∈ V := by
  obtain ⟨p, hp⟩ := exists_clusterPt_of_compactSpace (map f cofinite)
  have hd : {z : K × K | z.1 - z.2 ∈ V} ∈ 𝓝 (p, p) := by
    exact continuous_sub.continuousAt.preimage_mem_nhds (by simpa using hV)
  obtain ⟨U, hU, W, hW, hUW⟩ := mem_nhds_prod_iff.mp hd
  have hw : ∃ᶠ a in cofinite, f a ∈ W := hp.frequently hW
  obtain ⟨a, ha⟩ := hw.exists
  have hu : ∃ᶠ b in cofinite, f b ∈ U := hp.frequently hU
  obtain ⟨b, hb, hgood⟩ := (hu.and_eventually (hbad a).eventually_cofinite_notMem).exists
  exact ⟨a, b, hgood, hUW (a := (f b, f a)) ⟨hb, ha⟩⟩

private lemma dense_of_reflections {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] (hnd : ‹TopologicalSpace G› ≠ ⊥)
    (hfin : {z : G | z ^ 2 = 1}.Finite) [CompactSpace K] (e : Additive G →+ K)
    (he : Function.Injective e) (c : K → Bool)
    (hc : ∀ g : G, ∀ᶠ v in 𝓝 0, v ≠ -v →
      c (e (Additive.ofMul g) + v) ≠ c (e (Additive.ofMul g) + -v)) (color : Bool) :
    Dense {x : G | c (e (Additive.ofMul x)) = color} := by
  intro g
  apply mem_closure_iff_nhds.2
  intro O hO
  -- Restrict both ends of a difference so either reflected point belongs to O.
  have hcont : Continuous (fun z : G × G ↦ g * (z.1 / z.2)) := by fun_prop
  have hmem := hcont.continuousAt.preimage_mem_nhds (x := ((1 : G), 1)) (t := O)
    (by simpa using hO)
  obtain ⟨U, hU, W, hW, hUW⟩ := mem_nhds_prod_iff.mp hmem
  let A := U ∩ W
  have : Infinite A := infinite_coe_iff.2 fun hf ↦
    hnd (discreteTopology_of_isOpen_singleton_one
      (isOpen_singleton_of_finite_mem_nhds 1 (inter_mem hU hW) hf)).eq_bot
  let bad (a : A) : Set A := (fun b : A ↦ (b : G) / a) ⁻¹' {z | z ^ 2 = 1}
  have hbad (a : A) : (bad a).Finite :=
    hfin.preimage ((div_left_injective (b := (a : G))).comp Subtype.val_injective).injOn
  obtain ⟨a, b, hab, hv⟩ := close_pair (fun a : A ↦ e (Additive.ofMul (a : G))) bad hbad (hc g)
  let v := e (Additive.ofMul (b : G)) - e (Additive.ofMul (a : G))
  have hd : e (Additive.ofMul ((b : G) / a)) = v := map_sub e _ _
  have hne : v ≠ -v := by
    intro h
    rw [← hd, ← map_neg] at h
    have h' : (b : G) / a = ((b : G) / a)⁻¹ := congrArg Additive.toMul (he h)
    apply hab
    change ((b : G) / a) ^ 2 = 1
    simpa only [sq, mul_eq_one_iff_eq_inv] using h'
  have hp : c (e (Additive.ofMul g) + v) ≠ c (e (Additive.ofMul g) + -v) := hv hne
  have hcolors (z w : Bool) (hne : z ≠ w) : z = color ∨ w = color := by
    cases z <;> cases w <;> cases color <;> simp_all
  have memO (j k : A) : g * ((j : G) / k) ∈ O :=
    hUW (a := ((j : G), (k : G))) ⟨j.property.1, k.property.2⟩
  rcases hcolors _ _ hp with h | h
  · refine ⟨g * ((b : G) / a), memO b a, ?_⟩
    change c (e (Additive.ofMul g + Additive.ofMul ((b : G) / a))) = color
    rwa [map_add, hd]
  · refine ⟨g * ((a : G) / b), memO a b, ?_⟩
    change c (e (Additive.ofMul g + (Additive.ofMul (a : G) - Additive.ofMul (b : G)))) = color
    simpa only [map_add, map_sub, v, neg_sub] using h

/-- **Kourovka Problem 13.47 has a positive answer.** Every countable abelian group $G$ with only
finitely many elements of order $2$ can be partitioned into two disjoint sets $A_1$ and $A_2$ with
$A_1 \cup A_2 = G$ such that $A_1$ and $A_2$ are both dense in every non-discrete Hausdorff group
topology on $G$.

The Kourovka Archive answers 13.47 "Yes, it can", citing Zelenyuk.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 13.47 (I. V. Protasov); resolution: E. G. Zelenyuk, Ukrain. Math. J. 51
(1999), no. 1, 44-50, Kourovka Archive, Problem 13.47 (answer: Yes, it can).
-/
theorem countableAbsolutelyDensePartition_holds : countableAbsolutelyDensePartition := by
  classical
  intro G _ hcount hfinite
  obtain ⟨g, hg⟩ := exists_surjective_nat G
  let e := evaluation (G := Additive G)
  obtain ⟨c, hc⟩ := color_centers (fun n ↦ e (Additive.ofMul (g n)))
  let col (x : G) := c (e (Additive.ofMul x))
  refine ⟨{x | col x = true}, {x | col x = false}, ?_, ?_, ?_⟩
  · ext x
    cases h : col x <;> simp [h]
  · exact Set.disjoint_left.2 fun x ht hf ↦ Bool.noConfusion (ht.symm.trans hf)
  intro τ hT hnd
  let _ := τ.toTopologicalSpace
  have := τ.toIsTopologicalGroup
  have hfin : {z : G | z ^ 2 = 1}.Finite := (hfinite.insert 1).subset fun z hz ↦ by
    by_cases h : z = 1
    · exact Or.inl h
    · exact Or.inr ⟨h, hz⟩
  have hall (x : G) := (hg x).choose_spec ▸ hc (hg x).choose
  exact ⟨dense_of_reflections hnd hfin e evaluation_injective c hall true,
    dense_of_reflections hnd hfin e evaluation_injective c hall false⟩

end MathlibExt.GroupTheory.AbsolutelyDensePartitionKourovka13Problem47Wanted
