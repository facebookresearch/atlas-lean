/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.ClusterMerging
public import MathlibExt.Probability.Configuration.BernoulliErgodicity
public import MathlibExt.Probability.Percolation.Theta
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.UniqueInfiniteComponent

/-!
# Finite modifications of Bernoulli bond percolation

Forcing a finite edge pattern preserves null events at interior densities. Opening a box merges
two infinite clusters meeting it. Lattice translations act ergodically in positive dimension.

The finite-modification argument follows `BurtonKeaneMergeGeom` and `BurtonKeaneClose` in the
archived ATLAS statistical mechanics development.
-/

namespace MathlibExt.Probability.Percolation.BurtonKeaneWanted

open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation
open MeasureTheory Filter Topology
open scoped NNReal ENNReal BigOperators

noncomputable section

/-! ## Connecting sites inside an open box -/

section

open Set
variable {d : ℕ}

/-- The subgraph of the hypercubic lattice induced by a box is preconnected. -/
public theorem box_preconnected (n : ℕ) :
    ((hypercubicLattice d).induce (box d n)).Preconnected := by
  classical
  intro x y
  let mix (s : Finset (Fin d)) : Site d := fun i => if i ∈ s then y.1 i else x.1 i
  have hbox (s : Finset (Fin d)) : mix s ∈ box d n := by
    intro i
    by_cases hi : i ∈ s <;> simp only [mix, hi, ite_true, ite_false]
    · exact y.2 i
    · exact x.2 i
  have hreach (s : Finset (Fin d)) :
      ((hypercubicLattice d).induce (box d n)).Reachable x ⟨mix s, hbox s⟩ := by
    induction s using Finset.induction_on with
    | empty => simp [mix]
    | insert j s hj ih =>
      have heq : Function.update (mix s) j (y.1 j) = mix (insert j s) := by
        ext i
        by_cases hi : i = j <;> simp [mix, hi, Function.update]
      have hseg (z : ℤ) (hz : min (mix s j) (y.1 j) ≤ z ∧ z ≤ max (mix s j) (y.1 j)) :
          Function.update (mix s) j z ∈ box d n := by
        intro i
        by_cases hi : i = j
        · subst i
          rw [Function.update_self]
          have h₁ := hbox s j
          have h₂ := y.2 j
          omega
        · rw [Function.update_of_ne hi]
          exact hbox s i
      have hr := segment_gen (box d n) j (mix s) (y.1 j) (hbox s) (heq ▸ hbox _) hseg
      exact ih.trans (by simpa only [heq] using hr)
  simpa [mix] using hreach Finset.univ

noncomputable def boxPairs (d n : ℕ) : Finset (Sym2 (Site d)) :=
  ((boxFinset d n) ×ˢ (boxFinset d n)).image (fun p => s(p.1, p.2))

lemma mk_mem_boxPairs {n : ℕ} {x y : Site d} (hx : x ∈ box d n) (hy : y ∈ box d n) :
    s(x, y) ∈ boxPairs d n :=
  Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr
    ⟨mem_boxFinset.mpr hx, mem_boxFinset.mpr hy⟩, rfl⟩

lemma box_allOpen_connected {n : ℕ} (ω : ConfigSpace (Sym2 (Site d)))
    {x y : Site d} (hx : x ∈ box d n) (hy : y ∈ box d n) :
    Connected d (forceOpenFinset (boxPairs d n) ω) x y := by
  let f : (hypercubicLattice d).induce (box d n) →g
      openSubgraph d (forceOpenFinset (boxPairs d n) ω) :=
    { toFun := Subtype.val
      map_rel' := fun {a b} hab =>
        ⟨hab, forceOpenFinset_of_mem (mk_mem_boxPairs a.2 b.2) ω⟩ }
  exact (box_preconnected n ⟨x, hx⟩ ⟨y, hy⟩).map f

end

/-! ## Merging a finite number of infinite clusters -/

section

open MeasureTheory Set
open scoped ENNReal BigOperators
variable {d : ℕ}

def twoMeetBox (d n : ℕ) (k : ℕ∞) : Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | numInfiniteClusters d ω = k ∧
    ∃ x y : Site d, x ∈ box d n ∧ y ∈ box d n ∧
      (cluster d ω x).Infinite ∧ (cluster d ω y).Infinite ∧
      cluster d ω x ≠ cluster d ω y}

theorem twoMeetBox_subset_mergeWitness (n : ℕ) (k : ℕ∞) :
    twoMeetBox d n k ⊆ MergeWitness d (boxPairs d n) k := by
  rintro ω ⟨hkeq, x, y, hx, hy, hxinf, hyinf, hne⟩
  refine ⟨hkeq, x, y, hxinf, hyinf, hne, ?_⟩
  exact box_allOpen_connected ω hx hy

theorem count_level_subset_iUnion_twoMeetBox {k : ℕ∞} (hk2 : 2 ≤ k) :
    {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω = k}
      ⊆ ⋃ n, twoMeetBox d n k := by
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω
  have hcard : (2 : ℕ∞) ≤ (infiniteClusters d ω).encard := by
    have heq : numInfiniteClusters d ω = (infiniteClusters d ω).encard := rfl
    rw [heq] at hω; rw [hω]; exact hk2
  have hnt : (infiniteClusters d ω).Nontrivial := by
    apply Set.one_lt_encard_iff_nontrivial.mp
    exact lt_of_lt_of_le (by decide : (1 : ℕ∞) < 2) hcard
  obtain ⟨C₁, hC₁mem, C₂, hC₂mem, hCne⟩ := hnt
  simp only [infiniteClusters, Set.mem_ofPred_eq] at hC₁mem hC₂mem
  obtain ⟨hinf1, x, hxeq⟩ := hC₁mem
  obtain ⟨hinf2, y, hyeq⟩ := hC₂mem
  have hxinf : (cluster d ω x).Infinite := by rw [← hxeq]; exact hinf1
  have hyinf : (cluster d ω y).Infinite := by rw [← hyeq]; exact hinf2
  have hclne : cluster d ω x ≠ cluster d ω y := by rw [← hxeq, ← hyeq]; exact hCne
  obtain ⟨n, hn⟩ := finite_subset_box ({x, y} : Set (Site d)) (Set.toFinite _)
  have hxbox : x ∈ box d n := hn (Set.mem_insert x {y})
  have hybox : y ∈ box d n := hn (Set.mem_insert_of_mem x rfl)
  exact Set.mem_iUnion.mpr ⟨n, hω, x, y, hxbox, hybox, hxinf, hyinf, hclne⟩

theorem exists_twoMeetBox_pos
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    {k : ℕ∞} (hk2 : 2 ≤ k) (hk : μ {ω | numInfiniteClusters d ω = k} = 1) :
    ∃ n : ℕ, 0 < μ (twoMeetBox d n k) := by
  by_contra hcon
  simp only [not_exists, not_lt, nonpos_iff_eq_zero] at hcon
  have hunion0 : μ (⋃ n, twoMeetBox d n k) = 0 := by
    refine le_antisymm ?_ bot_le
    calc μ (⋃ n, twoMeetBox d n k) ≤ ∑' n, μ (twoMeetBox d n k) :=
          measure_iUnion_le _
      _ = 0 := by simp [hcon]
  have hle : μ {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω = k}
      ≤ μ (⋃ n, twoMeetBox d n k) :=
    measure_mono (count_level_subset_iUnion_twoMeetBox hk2)
  rw [hk, hunion0] at hle
  exact absurd hle (by norm_num)

/-- If a finite box meets two infinite clusters, opening its edges joins them. Some such
box has positive probability whenever the almost sure cluster count is at least two. -/
public theorem exists_mergeWitness_pos
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (k : ℕ∞) (hk2 : 2 ≤ k)
    (hk : μ {ω | numInfiniteClusters d ω = k} = 1) :
    ∃ F : Finset (Sym2 (Site d)), 0 < μ (MergeWitness d F k) := by
  obtain ⟨n, hpos⟩ := exists_twoMeetBox_pos μ hk2 hk
  refine ⟨boxPairs d n, lt_of_lt_of_le hpos ?_⟩
  exact measure_mono (twoMeetBox_subset_mergeWitness n k)

end

/-! ## Changing finitely many Bernoulli coordinates and ergodicity -/

section

open MeasureTheory Measure Set MeasurableSpace ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology BigOperators
variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

theorem infinitePi_disjoint_cylinder
    (μ : (i : ι) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    {s t : Finset ι} {S : Set (Π i : s, X i)} {T : Set (Π i : t, X i)}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hd : Disjoint s t) :
    Measure.infinitePi μ (cylinder s S ∩ cylinder t T)
      = Measure.infinitePi μ (cylinder s S) * Measure.infinitePi μ (cylinder t T) := by
  have hind : iIndepFun (fun i (ω : Π i, X i) => ω i) (Measure.infinitePi μ) :=
    iIndepFun_infinitePi (𝓧 := X) (X := fun _ x => x) (fun i => measurable_id)
  exact
    (hind.indepFun_finset s t hd (fun e => measurable_pi_apply e)).measure_inter_preimage_eq_mul
      S T hS hT
omit [∀ i, MeasurableSpace (X i)] in
theorem projP_preimage_cylinder (p : ι → Prop) (s : Finset (Subtype p))
    (S : Set (Π j : s, X ((j : Subtype p) : ι))) :
    (fun (ω : Π i, X i) (j' : Subtype p) => ω (j' : ι)) ⁻¹' (cylinder s S)
      = cylinder (s.map (Function.Embedding.subtype p))
          ((fun (y : Π i : s.map (Function.Embedding.subtype p), X (i : ι)) (j : s) =>
              y ⟨((j : Subtype p) : ι),
                by rw [Finset.mem_map]; exact ⟨(j : Subtype p), j.2, rfl⟩⟩) ⁻¹' S) := by
  ext ω; simp only [Set.mem_preimage, mem_cylinder]; rfl

theorem infinitePi_map_piEquivPiSubtypeProd
    (μ : (i : ι) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (p : ι → Prop) [DecidablePred p] :
    (Measure.infinitePi μ).map (MeasurableEquiv.piEquivPiSubtypeProd X p)
      = (Measure.infinitePi (fun j : Subtype p => μ (j : ι))).prod
          (Measure.infinitePi (fun j : {i // ¬ p i} => μ (j : ι))) := by
  classical
  symm
  refine Measure.prod_eq_generateFrom generateFrom_measurableCylinders
    generateFrom_measurableCylinders isPiSystem_measurableCylinders isPiSystem_measurableCylinders
    ⟨fun _ => univ, fun _ => univ_mem_measurableCylinders _, fun _ => by simp,
      by rw [iUnion_const]⟩
    ⟨fun _ => univ, fun _ => univ_mem_measurableCylinders _, fun _ => by simp,
      by rw [iUnion_const]⟩
    ?_
  intro A hA B hB
  rw [mem_measurableCylinders] at hA hB
  obtain ⟨s₁, S₁, hS₁, rfl⟩ := hA
  obtain ⟨s₂, S₂, hS₂, rfl⟩ := hB
  rw [Measure.map_apply (MeasurableEquiv.piEquivPiSubtypeProd X p).measurable
    ((MeasurableSet.cylinder _ hS₁).prod (MeasurableSet.cylinder _ hS₂))]
  have hpre : (MeasurableEquiv.piEquivPiSubtypeProd X p) ⁻¹' (cylinder s₁ S₁ ×ˢ cylinder s₂ S₂)
      = ((fun (ω : Π i, X i) (j : Subtype p) => ω (j : ι)) ⁻¹' (cylinder s₁ S₁)) ∩
        ((fun (ω : Π i, X i) (j : {i // ¬ p i}) => ω (j : ι)) ⁻¹' (cylinder s₂ S₂)) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_inter_iff]
    rfl
  rw [hpre, projP_preimage_cylinder p s₁ S₁,
    projP_preimage_cylinder (fun i => ¬ p i) s₂ S₂]
  rw [infinitePi_disjoint_cylinder μ (?_) (?_) (?_)]
  · congr 1
    · rw [← projP_preimage_cylinder p s₁ S₁,
        ← Measure.map_apply (by fun_prop) (MeasurableSet.cylinder _ hS₁),
        Measure.map_infinitePi_infinitePi_of_inj (f := (Subtype.val : Subtype p → ι))
          Subtype.val_injective]
    · rw [← projP_preimage_cylinder (fun i => ¬ p i) s₂ S₂,
        ← Measure.map_apply (by fun_prop) (MeasurableSet.cylinder _ hS₂),
        Measure.map_infinitePi_infinitePi_of_inj (f := (Subtype.val : {i // ¬ p i} → ι))
          Subtype.val_injective]
  · exact (by fun_prop : Measurable _) hS₁
  · exact (by fun_prop : Measurable _) hS₂
  · rw [Finset.disjoint_left]
    intro a ha1 ha2
    rw [Finset.mem_map] at ha1 ha2
    obtain ⟨j1, _, rfl⟩ := ha1
    obtain ⟨j2, _, hj2⟩ := ha2
    change (j2 : ι) = (j1 : ι) at hj2
    exact j2.2 (hj2 ▸ j1.2)

theorem pi_absolutelyContinuous_fin :
    ∀ (n : ℕ) {Y : Fin n → Type*} [∀ k, MeasurableSpace (Y k)]
      (ν μ : (k : Fin n) → Measure (Y k))
      [∀ k, IsProbabilityMeasure (μ k)] [∀ k, IsProbabilityMeasure (ν k)],
      (∀ k, ν k ≪ μ k) → Measure.pi ν ≪ Measure.pi μ := by
  intro n
  induction n with
  | zero =>
    intro Y _ ν μ _ _ _
    have heq : Measure.pi ν = Measure.pi μ := by
      ext s _
      rcases Set.eq_empty_or_nonempty s with rfl | ⟨x, hx⟩
      · simp
      · have hsu : s = Set.univ := by
          ext y; simp only [Set.mem_univ, iff_true]; rwa [Subsingleton.elim y x]
        rw [hsu, measure_univ, measure_univ]
    rw [heq]
  | succ n ih =>
    intro Y _ ν μ _ _ h
    set e := MeasurableEquiv.piFinSuccAbove Y 0 with he
    have hμ : Measure.pi μ
        = ((μ 0).prod (Measure.pi fun j => μ (Fin.succAbove 0 j))).map e.symm := by
      rw [← (measurePreserving_piFinSuccAbove μ 0).map_eq, ← he,
        Measure.map_map e.symm.measurable e.measurable, MeasurableEquiv.symm_comp_self,
        Measure.map_id]
    have hν : Measure.pi ν
        = ((ν 0).prod (Measure.pi fun j => ν (Fin.succAbove 0 j))).map e.symm := by
      rw [← (measurePreserving_piFinSuccAbove ν 0).map_eq, ← he,
        Measure.map_map e.symm.measurable e.measurable, MeasurableEquiv.symm_comp_self,
        Measure.map_id]
    rw [hμ, hν]
    exact (Measure.AbsolutelyContinuous.prod (h 0)
      (ih (fun j => ν (Fin.succAbove 0 j)) (fun j => μ (Fin.succAbove 0 j))
        (fun j => h _))).map e.symm.measurable

theorem pi_absolutelyContinuous_fintype {κ : Type*} [Fintype κ] {Y : κ → Type*}
    [∀ k, MeasurableSpace (Y k)] (ν μ : (k : κ) → Measure (Y k))
    [∀ k, IsProbabilityMeasure (μ k)] [∀ k, IsProbabilityMeasure (ν k)]
    (h : ∀ k, ν k ≪ μ k) : Measure.pi ν ≪ Measure.pi μ := by
  classical
  set ee := Fintype.equivFin κ with hee
  have hmpμ := measurePreserving_piCongrLeft (fun k => μ k) ee.symm
  have hmpν := measurePreserving_piCongrLeft (fun k => ν k) ee.symm
  have hfin := pi_absolutelyContinuous_fin (Fintype.card κ)
    (fun n => ν (ee.symm n)) (fun n => μ (ee.symm n)) (fun n => h _)
  rw [← hmpμ.map_eq, ← hmpν.map_eq]
  exact hfin.map (MeasurableEquiv.piCongrLeft Y ee.symm).measurable

theorem infinitePi_ac_of_finite_diff
    (ν μ : (i : ι) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, IsProbabilityMeasure (ν i)]
    (F : Finset ι) (hdiff : ∀ i ∉ F, ν i = μ i) (hac : ∀ i, ν i ≪ μ i) :
    Measure.infinitePi ν ≪ Measure.infinitePi μ := by
  classical
  set p : ι → Prop := fun i => i ∈ F with hp
  set e := MeasurableEquiv.piEquivPiSubtypeProd X p with he
  have hsμ := infinitePi_map_piEquivPiSubtypeProd μ p
  have hsν := infinitePi_map_piEquivPiSubtypeProd ν p
  have heqrest : (fun j : {i // ¬ p i} => ν (j : ι)) = (fun j : {i // ¬ p i} => μ (j : ι)) := by
    funext j; exact hdiff (j : ι) j.2
  have hprodac : ((Measure.infinitePi (fun j : Subtype p => ν (j : ι))).prod
          (Measure.infinitePi (fun j : {i // ¬ p i} => ν (j : ι))))
      ≪ ((Measure.infinitePi (fun j : Subtype p => μ (j : ι))).prod
          (Measure.infinitePi (fun j : {i // ¬ p i} => μ (j : ι)))) := by
    rw [heqrest]
    refine Measure.AbsolutelyContinuous.prod ?_ (Measure.absolutelyContinuous_refl _)
    have : Fintype (Subtype p) := Fintype.ofFinite _
    rw [Measure.infinitePi_eq_pi, Measure.infinitePi_eq_pi]
    exact pi_absolutelyContinuous_fintype _ _ (fun j => hac _)
  calc Measure.infinitePi ν
      = ((Measure.infinitePi ν).map e).map e.symm := by
        rw [Measure.map_map e.symm.measurable e.measurable, MeasurableEquiv.symm_comp_self,
          Measure.map_id]
    _ ≪ ((Measure.infinitePi μ).map e).map e.symm := by
        rw [hsμ, hsν]; exact hprodac.map e.symm.measurable
    _ = Measure.infinitePi μ := by
        rw [Measure.map_map e.symm.measurable e.measurable, MeasurableEquiv.symm_comp_self,
          Measure.map_id]
variable {d : ℕ}

theorem factor_ac (p : ℝ≥0) (hp : p ≤ 1) (hp0 : 0 < p) (e : Sym2 (Site d))
    (F : Finset (Sym2 (Site d))) :
    (bernoulliMeasure p hp).map (fun b => if e ∈ F then true else b) ≪ bernoulliMeasure p hp := by
  by_cases h : e ∈ F
  · simp only [h, ite_true]
    refine Measure.AbsolutelyContinuous.mk ?_
    intro s hs hs0
    rw [Measure.map_apply (by fun_prop) hs]
    by_cases ht : (true : Bool) ∈ s
    · exfalso
      have hsub : ({true} : Set Bool) ⊆ s := by rintro x rfl; exact ht
      have h1 : bernoulliMeasure p hp {true} ≤ bernoulliMeasure p hp s := measure_mono hsub
      rw [bernoulliMeasure_apply_true, hs0] at h1
      have hpz : (p : ℝ≥0∞) = 0 := le_antisymm h1 (by positivity)
      simp only [ENNReal.coe_eq_zero] at hpz
      exact hp0.ne' hpz
    · have hpre : (fun _ : Bool => true) ⁻¹' s = ∅ := by
        ext x; simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]; exact ht
      rw [hpre]; simp
  · simp only [h, ite_false]
    have he : (fun b : Bool => b) = id := rfl
    rw [he, Measure.map_id]

/-- At positive density, opening any finite set of edges preserves null events. -/
public theorem bernoulli_finiteEnergyMerge (p : ℝ≥0) (hp : p ≤ 1) (hp0 : 0 < p) :
    HasFiniteEnergyMerge (d := d) (bernoulliProductMeasure (E := Sym2 (Site d)) p hp) := by
  intro F
  have hmap : (fun (ω : ConfigSpace (Sym2 (Site d))) => forceOpenFinset F ω)
      = (fun (ω : ConfigSpace (Sym2 (Site d))) e =>
          (fun b => if e ∈ F then true else b) (ω e)) := by
    funext ω e; unfold forceOpenFinset; by_cases h : e ∈ F <;> simp [h]
  have hpush : (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).map
        (fun ω => forceOpenFinset F ω)
      = Measure.infinitePi
          (fun e => (bernoulliMeasure p hp).map (fun b => if e ∈ F then true else b)) := by
    rw [hmap]
    unfold bernoulliProductMeasure
    refine Measure.infinitePi_map_pi (μ := fun _ : Sym2 (Site d) => bernoulliMeasure p hp)
      (f := fun e (b : Bool) => if e ∈ F then true else b) (fun e => ?_)
    by_cases h : e ∈ F <;> simp only [h, ite_true, ite_false]
    · exact measurable_const
    · exact measurable_id
  rw [hpush]
  have hμ : bernoulliProductMeasure (E := Sym2 (Site d)) p hp
      = Measure.infinitePi (fun _ : Sym2 (Site d) => bernoulliMeasure p hp) := rfl
  rw [hμ]
  refine infinitePi_ac_of_finite_diff _ _ F (fun e he => ?_)
    (fun e => factor_ac p hp hp0 e F)
  simp only [he, ite_false]
  have he2 : (fun b : Bool => b) = id := rfl
  rw [he2, Measure.map_id]

theorem smul_sym2_injective (a : Sym2 (Site d)) :
    Function.Injective (fun g : Multiplicative (Site d) => g • a) := by
  intro g g' h
  simp only at h
  induction a with
  | h x y =>
    rw [smul_sym2_mk, smul_sym2_mk, Sym2.eq_iff] at h
    apply Multiplicative.toAdd.injective
    funext i
    rcases h with ⟨h1, _⟩ | ⟨h1, h2⟩
    · have := congrFun h1 i; simp only [smul_site_apply] at this; linarith
    · have e1 := congrFun h1 i
      have e2 := congrFun h2 i
      simp only [smul_site_apply] at e1 e2
      linarith

/-- Bernoulli bond configurations in positive dimension are ergodic under lattice translations. -/
public theorem bernoulli_lattice_ergodic (hd : 1 ≤ d) (p : ℝ≥0) (hp : p ≤ 1) :
    IsErgodic (G := Multiplicative (Site d))
      (bernoulliProductMeasure (E := Sym2 (Site d)) p hp) := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have : Infinite (Multiplicative (Site d)) := by unfold Site; infer_instance
  exact StatMech.FK.bernoulli_isErgodic (E := Sym2 (Site d)) (G := Multiplicative (Site d))
    smul_sym2_injective p hp

end

/-! ## Prescribing an arbitrary edge pattern -/

section

open MeasureTheory Finset
variable {V : Type*} [DecidableEq V]

/-- Replace the states of the edges in `I` by the prescribed pattern `eta`. -/
@[expose] public noncomputable def setPattern (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I)
    (psi : ConfigSpace (Sym2 V)) : ConfigSpace (Sym2 V) :=
  fun e => if he : e ∈ I then eta ⟨e, he⟩ else psi e

/-- A prescribed edge takes the value assigned by the pattern. -/
@[simp] public theorem setPattern_of_mem {I : Finset (Sym2 V)} (eta : ConfigSpace ↥I)
    {e : Sym2 V} (he : e ∈ I) (psi : ConfigSpace (Sym2 V)) :
    setPattern I eta psi e = eta ⟨e, he⟩ := by
  simp [setPattern, he]

/-- An edge outside the pattern keeps its original value. -/
public theorem setPattern_of_not_mem {I : Finset (Sym2 V)} (eta : ConfigSpace ↥I)
    {e : Sym2 V} (he : e ∉ I) (psi : ConfigSpace (Sym2 V)) :
    setPattern I eta psi e = psi e := by
  simp [setPattern, he]
open MeasureTheory Set Filter Topology SimpleGraph
open scoped BigOperators symmDiff
variable {d : ℕ}

/-- Prescribing the states of finitely many bonds is a measurable operation. -/
public theorem measurable_setPattern {V : Type*} [DecidableEq V]
    (I : Finset (Sym2 V)) (eta : ConfigSpace ↥I) :
    Measurable (setPattern I eta :
      ConfigSpace (Sym2 V) → ConfigSpace (Sym2 V)) := by
  apply Measurable.of_eval
  intro e
  by_cases he : e ∈ I
  · rw [show (fun omega => setPattern I eta omega e) =
        fun _ => eta ⟨e, he⟩ by
      funext omega
      exact setPattern_of_mem eta he omega]
    exact measurable_const
  · rw [show (fun omega => setPattern I eta omega e) = fun omega => omega e by
      funext omega
      exact setPattern_of_not_mem eta he omega]
    exact measurable_pi_apply e

/-- At a density strictly between zero and one, prescribing any finite pattern preserves
Bernoulli null events. -/
public theorem map_setPattern_absolutelyContinuous {d : ℕ} {p : ℝ≥0} (hp0 : 0 < p) (hp1 : p < 1)
    (F : Finset (Sym2 (Site d))) (η : ConfigSpace ↥F) :
    (bernoulliProductMeasure p hp1.le).map (setPattern F η) ≪ bernoulliProductMeasure p hp1.le := by
  classical
  let f (e : Sym2 (Site d)) (b : Bool) := if h : e ∈ F then η ⟨e, h⟩ else b
  let μ := bernoulliMeasure p hp1.le
  have hm (e) : Measurable (f e) := Measurable.of_discrete
  change (Measure.infinitePi (fun _ => μ)).map (fun ω e => f e (ω e)) ≪ _
  rw [Measure.infinitePi_map_pi _ hm]
  apply infinitePi_ac_of_finite_diff _ _ F
  · intro i hi
    have h : f i = id := by ext b; simp [f, hi]
    rw [h, Measure.map_id]
  · intro i s hs
    have hmass (b : Bool) : μ {b} ≠ 0 := by
      cases b
      · simpa only [μ, bernoulliMeasure_apply_false, ENNReal.coe_ne_zero] using
          (tsub_pos_of_lt hp1).ne'
      · simpa [μ] using hp0.ne'
    have hempty : s = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun b hb =>
      hmass b (measure_mono_null (Set.singleton_subset_iff.mpr hb) hs)
    simp [hempty]

end

end

end MathlibExt.Probability.Percolation.BurtonKeaneWanted
