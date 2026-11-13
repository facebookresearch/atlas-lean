/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardPortChainGeneral
import Mathlib.Analysis.Convex.StrictConvexSpace










namespace StatMech.FrontierA

open Set SimpleGraph
open scoped NNReal ENNReal


def KWStraightLineEmbedding.dartClosedEdge
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (d : G.Dart) : Set ℂ :=
  segment ℝ (embedding.vertex d.fst) (embedding.vertex d.snd)

theorem KWStraightLineEmbedding.dartClosedEdge_isCompact
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (d : G.Dart) :
    IsCompact (embedding.dartClosedEdge d) := by
  rw [KWStraightLineEmbedding.dartClosedEdge, segment_eq_image_lineMap]
  exact isCompact_Icc.image AffineMap.lineMap_continuous

theorem KWStraightLineEmbedding.dartClosedEdge_isClosed
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (d : G.Dart) :
    IsClosed (embedding.dartClosedEdge d) :=
  (embedding.dartClosedEdge_isCompact d).isClosed

theorem KWStraightLineEmbedding.vertex_not_mem_dartClosedEdge
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (v : V) (d : G.Dart)
    (hvfst : v ≠ d.fst) (hvsnd : v ≠ d.snd) :
    embedding.vertex v ∉ embedding.dartClosedEdge d := by
  intro hmem
  have hbetween : Wbtw ℝ (embedding.vertex d.fst) (embedding.vertex v)
      (embedding.vertex d.snd) := mem_segment_iff_wbtw.mp hmem
  exact embedding.vertex_not_strictly_between d v hvfst hvsnd
    ⟨hbetween, embedding.vertex_injective.ne hvfst,
      embedding.vertex_injective.ne hvsnd⟩

theorem KWStraightLineEmbedding.singleton_vertex_disjoint_dartClosedEdge
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (v : V) (d : G.Dart)
    (hvfst : v ≠ d.fst) (hvsnd : v ≠ d.snd) :
    Disjoint ({embedding.vertex v} : Set ℂ) (embedding.dartClosedEdge d) :=
  Set.disjoint_singleton_left.mpr
    (embedding.vertex_not_mem_dartClosedEdge v d hvfst hvsnd)

private theorem kw_exists_uniform_nnreal_finset
    {α : Type*} (s : Finset α) (Q : α → ℝ≥0 → Prop)
    (hQ : ∀ a ∈ s, ∃ r : ℝ≥0, 0 < r ∧ Q a r)
    (hmono : ∀ a ∈ s, ∀ {r r' : ℝ≥0}, r' ≤ r → Q a r → Q a r') :
    ∃ r : ℝ≥0, 0 < r ∧ ∀ a ∈ s, Q a r := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert a s ha ih =>
      obtain ⟨ra, hra, hQa⟩ := hQ a (by simp)
      obtain ⟨rs, hrs, hQs⟩ := ih
        (fun b hb ↦ hQ b (by simp [hb]))
        (fun b hb r r' hle h ↦ hmono b (by simp [hb]) hle h)
      refine ⟨min ra rs, lt_min hra hrs, ?_⟩
      intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hbs
      · exact hmono _ (by simp) (min_le_left _ _) hQa
      · exact hmono b (by simp [hbs]) (min_le_right _ _) (hQs b hbs)

theorem KWStraightLineEmbedding.exists_uniform_vertex_separation
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) :
    ∃ r : ℝ≥0, 0 < r ∧ ∀ v w : V, v ≠ w →
      (r : ℝ) < dist (embedding.vertex v) (embedding.vertex w) := by
  classical
  let pairs : Finset (V × V) :=
    Finset.univ.filter (fun p ↦ p.1 ≠ p.2)
  let Q : (V × V) → ℝ≥0 → Prop := fun p r ↦
    (r : ℝ≥0∞) < edist (embedding.vertex p.1) (embedding.vertex p.2)
  have hpair : ∀ p ∈ pairs, ∃ r : ℝ≥0, 0 < r ∧ Q p r := by
    intro p hp
    have hne : p.1 ≠ p.2 := by
      simpa only [pairs, Finset.mem_filter, Finset.mem_univ, true_and] using hp
    obtain ⟨r, hr, hsep⟩ := Metric.exists_pos_forall_lt_edist
      (s := {embedding.vertex p.1}) (t := {embedding.vertex p.2})
      isCompact_singleton isClosed_singleton
      (Set.disjoint_singleton.mpr (embedding.vertex_injective.ne hne))
    refine ⟨r, hr, ?_⟩
    simpa [Q] using
      hsep (embedding.vertex p.1) rfl (embedding.vertex p.2) rfl
  have hmono : ∀ p ∈ pairs, ∀ {r r' : ℝ≥0},
      r' ≤ r → Q p r → Q p r' := by
    intro p _ r r' hle h
    exact (ENNReal.coe_le_coe.mpr hle).trans_lt h
  obtain ⟨r, hr, hruniform⟩ :=
    kw_exists_uniform_nnreal_finset pairs Q hpair hmono
  refine ⟨r, hr, ?_⟩
  intro v w hvw
  have h := hruniform (v, w) (by simp [pairs, hvw])
  dsimp only [Q] at h
  rw [edist_dist] at h
  exact ENNReal.coe_lt_ofReal.mp h

theorem KWStraightLineEmbedding.exists_uniform_edge_length
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) :
    ∃ r : ℝ≥0, 0 < r ∧ ∀ d : G.Dart,
      (r : ℝ) < ‖embedding.vertex d.snd - embedding.vertex d.fst‖ := by
  classical
  let Q : G.Dart → ℝ≥0 → Prop := fun d r ↦
    (r : ℝ) < ‖embedding.vertex d.snd - embedding.vertex d.fst‖
  have hQ : ∀ d ∈ (Finset.univ : Finset G.Dart),
      ∃ r : ℝ≥0, 0 < r ∧ Q d r := by
    intro d _
    let length : ℝ := ‖embedding.vertex d.snd - embedding.vertex d.fst‖
    have hlength : 0 < length := norm_pos_iff.mpr (embedding.dartVector_ne_zero d)
    let r : ℝ≥0 := ⟨length / 2, by positivity⟩
    refine ⟨r, ?_, ?_⟩
    · exact_mod_cast half_pos hlength
    · change length / 2 < length
      linarith
  have hmono : ∀ d ∈ (Finset.univ : Finset G.Dart), ∀ {r r' : ℝ≥0},
      r' ≤ r → Q d r → Q d r' := by
    intro d _ r r' hle h
    have hle' : (r' : ℝ) ≤ (r : ℝ) := by exact_mod_cast hle
    exact hle'.trans_lt h
  obtain ⟨r, hr, hall⟩ := kw_exists_uniform_nnreal_finset
    (Finset.univ : Finset G.Dart) Q hQ hmono
  exact ⟨r, hr, fun d ↦ hall d (Finset.mem_univ d)⟩

theorem KWStraightLineEmbedding.exists_uniform_vertex_edge_separation
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) :
    ∃ r : ℝ≥0, 0 < r ∧
      ∀ (v : V) (d : G.Dart), v ≠ d.fst → v ≠ d.snd →
        ∀ y ∈ embedding.dartClosedEdge d,
          (r : ℝ) < dist (embedding.vertex v) y := by
  classical
  let pairs : Finset (V × G.Dart) := Finset.univ.filter
    (fun p ↦ p.1 ≠ p.2.fst ∧ p.1 ≠ p.2.snd)
  let Q : (V × G.Dart) → ℝ≥0 → Prop := fun p r ↦
    ∀ y ∈ embedding.dartClosedEdge p.2,
      (r : ℝ≥0∞) < edist (embedding.vertex p.1) y
  have hpair : ∀ p ∈ pairs, ∃ r : ℝ≥0, 0 < r ∧ Q p r := by
    intro p hp
    have hnon : p.1 ≠ p.2.fst ∧ p.1 ≠ p.2.snd := by
      simpa only [pairs, Finset.mem_filter, Finset.mem_univ, true_and] using hp
    obtain ⟨r, hr, hsep⟩ := Metric.exists_pos_forall_lt_edist
      (s := {embedding.vertex p.1}) (t := embedding.dartClosedEdge p.2)
      isCompact_singleton (embedding.dartClosedEdge_isClosed p.2)
      (embedding.singleton_vertex_disjoint_dartClosedEdge
        p.1 p.2 hnon.1 hnon.2)
    exact ⟨r, hr, fun y hy ↦ hsep (embedding.vertex p.1) rfl y hy⟩
  have hmono : ∀ p ∈ pairs, ∀ {r r' : ℝ≥0},
      r' ≤ r → Q p r → Q p r' := by
    intro p _ r r' hle h y hy
    exact (ENNReal.coe_le_coe.mpr hle).trans_lt (h y hy)
  obtain ⟨r, hr, hall⟩ :=
    kw_exists_uniform_nnreal_finset pairs Q hpair hmono
  refine ⟨r, hr, ?_⟩
  intro v d hvfst hvsnd y hy
  have h := hall (v, d) (by simp [pairs, hvfst, hvsnd]) y hy
  rw [edist_dist] at h
  exact ENNReal.coe_lt_ofReal.mp h



structure KWAngularPortRadiusData
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) where
  radius : ℝ≥0
  radius_pos : 0 < radius
  vertex_separated : ∀ v w : V, v ≠ w →
    4 * (radius : ℝ) < dist (embedding.vertex v) (embedding.vertex w)
  edge_long : ∀ d : G.Dart,
    4 * (radius : ℝ) <
      ‖embedding.vertex d.snd - embedding.vertex d.fst‖
  vertex_edge_separated : ∀ (v : V) (d : G.Dart),
    v ≠ d.fst → v ≠ d.snd →
      ∀ y ∈ embedding.dartClosedEdge d,
        2 * (radius : ℝ) < dist (embedding.vertex v) y

theorem KWStraightLineEmbedding.exists_angularPortRadiusData
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) :
    Nonempty (KWAngularPortRadiusData embedding) := by
  obtain ⟨rv, hrv, hv⟩ := embedding.exists_uniform_vertex_separation
  obtain ⟨re, hre, he⟩ := embedding.exists_uniform_edge_length
  obtain ⟨rve, hrve, hve⟩ := embedding.exists_uniform_vertex_edge_separation
  let R : ℝ≥0 := min rv (min re rve) / 8
  have hR : 0 < R := by
    dsimp only [R]
    positivity
  refine ⟨⟨R, hR, ?_, ?_, ?_⟩⟩
  · intro v w hvw
    have hle : R ≤ rv / 8 := by
      dsimp only [R]
      gcongr
      exact min_le_left _ _
    have hcast : (R : ℝ) ≤ (rv : ℝ) / 8 := by exact_mod_cast hle
    have := hv v w hvw
    have hrv0 : 0 < (rv : ℝ) := by exact_mod_cast hrv
    linarith
  · intro d
    have hle : R ≤ re / 8 := by
      dsimp only [R]
      gcongr
      exact (min_le_right rv (min re rve)).trans (min_le_left re rve)
    have hcast : (R : ℝ) ≤ (re : ℝ) / 8 := by exact_mod_cast hle
    have := he d
    have hre0 : 0 < (re : ℝ) := by exact_mod_cast hre
    linarith
  · intro v d hvfst hvsnd y hy
    have hle : R ≤ rve / 8 := by
      dsimp only [R]
      gcongr
      exact (min_le_right rv (min re rve)).trans (min_le_right re rve)
    have hcast : (R : ℝ) ≤ (rve : ℝ) / 8 := by exact_mod_cast hle
    have := hve v d hvfst hvsnd y hy
    have hrve0 : 0 < (rve : ℝ) := by exact_mod_cast hrve
    linarith


noncomputable def KWStraightLineEmbedding.dartUnit
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (d : G.Dart) : ℂ :=
  (embedding.vertex d.snd - embedding.vertex d.fst) /
    ‖embedding.vertex d.snd - embedding.vertex d.fst‖


noncomputable def kwAngularPortVertex
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (r : ℝ) (p : KWDartPort G) : ℂ :=
  embedding.vertex p.1 +
    (r : ℂ) * embedding.dartUnit (kwDartOfPort G p)

@[simp] theorem KWStraightLineEmbedding.norm_dartUnit
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (d : G.Dart) :
    ‖embedding.dartUnit d‖ = 1 := by
  unfold KWStraightLineEmbedding.dartUnit
  rw [norm_div]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_norm]
  exact div_self (norm_ne_zero_iff.mpr (embedding.dartVector_ne_zero d))

theorem KWStraightLineEmbedding.dartUnit_ne_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (d : G.Dart) :
    embedding.dartUnit d ≠ 0 := by
  intro h
  have := embedding.norm_dartUnit d
  rw [h, norm_zero] at this
  norm_num at this

theorem KWStraightLineEmbedding.dartUnit_eq_iff_arg_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (d e : G.Dart) :
    embedding.dartUnit d = embedding.dartUnit e ↔
      Complex.arg (embedding.vertex d.snd - embedding.vertex d.fst) =
        Complex.arg (embedding.vertex e.snd - embedding.vertex e.fst) := by
  let x := embedding.vertex d.snd - embedding.vertex d.fst
  let y := embedding.vertex e.snd - embedding.vertex e.fst
  have hx : x ≠ 0 := by
    simpa only [x] using embedding.dartVector_ne_zero d
  have hy : y ≠ 0 := by
    simpa only [y] using embedding.dartVector_ne_zero e
  unfold KWStraightLineEmbedding.dartUnit
  change x / (‖x‖ : ℂ) = y / (‖y‖ : ℂ) ↔
    Complex.arg x = Complex.arg y
  have hrayarg : SameRay ℝ x y ↔ Complex.arg x = Complex.arg y := by
    simpa only [Complex.sameRay_iff, hx, hy, false_or]
  rw [← hrayarg]
  rw [sameRay_iff_inv_norm_smul_eq_of_ne hx hy]
  simp only [div_eq_inv_mul, Complex.real_smul, Complex.ofReal_inv]

theorem KWStraightLineEmbedding.dartUnit_ne_of_outgoing
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) {d e : G.Dart}
    (hfst : d.fst = e.fst) (hne : d ≠ e) :
    embedding.dartUnit d ≠ embedding.dartUnit e := by
  intro hunit
  have harg := (embedding.dartUnit_eq_iff_arg_eq d e).mp hunit
  apply embedding.outgoing_dartAngle_ne hfst hne
  unfold KWStraightLineEmbedding.dartAngle
  rw [harg]

@[simp] theorem KWStraightLineEmbedding.dartUnit_symm
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (d : G.Dart) :
    embedding.dartUnit d.symm = -embedding.dartUnit d := by
  unfold KWStraightLineEmbedding.dartUnit
  have hvec : embedding.vertex d.fst - embedding.vertex d.snd =
      -(embedding.vertex d.snd - embedding.vertex d.fst) := by ring
  change (embedding.vertex d.fst - embedding.vertex d.snd) /
      (‖embedding.vertex d.fst - embedding.vertex d.snd‖ : ℂ) =
    -((embedding.vertex d.snd - embedding.vertex d.fst) /
      (‖embedding.vertex d.snd - embedding.vertex d.fst‖ : ℂ))
  rw [hvec, norm_neg]
  ring

theorem KWStraightLineEmbedding.dartVector_eq_norm_mul_dartUnit
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (d : G.Dart) :
    embedding.vertex d.snd - embedding.vertex d.fst =
      (‖embedding.vertex d.snd - embedding.vertex d.fst‖ : ℂ) *
        embedding.dartUnit d := by
  unfold KWStraightLineEmbedding.dartUnit
  have hnorm : (‖embedding.vertex d.snd - embedding.vertex d.fst‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr (embedding.dartVector_ne_zero d)
  exact (mul_div_cancel₀ _ hnorm).symm

@[simp] theorem dist_kwAngularPortVertex_owner
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (r : ℝ) (p : KWDartPort G) :
    dist (kwAngularPortVertex embedding r p) (embedding.vertex p.1) = |r| := by
  unfold kwAngularPortVertex
  rw [dist_eq_norm, add_sub_cancel_left, norm_mul,
    embedding.norm_dartUnit, mul_one]
  simp

theorem kwAngularPortVertex_sub_owner
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (r : ℝ) (p : KWDartPort G) :
    kwAngularPortVertex embedding r p - embedding.vertex p.1 =
      (r : ℂ) * embedding.dartUnit (kwDartOfPort G p) := by
  unfold kwAngularPortVertex
  ring

theorem kwAngularPortVertex_matching_sub
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (r : ℝ)
    {p q : KWDartPort G}
    (hmatching : kwDartOfPort G q = (kwDartOfPort G p).symm) :
    kwAngularPortVertex embedding r q - kwAngularPortVertex embedding r p =
      ((‖embedding.vertex (kwDartOfPort G p).snd -
          embedding.vertex (kwDartOfPort G p).fst‖ - 2 * r : ℝ) : ℂ) *
        embedding.dartUnit (kwDartOfPort G p) := by
  let d := kwDartOfPort G p
  have hp : p.1 = d.fst := (kwDartOfPort_fst G p).symm
  have hq : q.1 = d.snd := by
    calc
      q.1 = (kwDartOfPort G q).fst := (kwDartOfPort_fst G q).symm
      _ = d.symm.fst := by rw [hmatching]
      _ = d.snd := rfl
  unfold kwAngularPortVertex
  rw [hp, hq, hmatching, embedding.dartUnit_symm]
  change embedding.vertex d.snd + (r : ℂ) * -embedding.dartUnit d -
      (embedding.vertex d.fst + (r : ℂ) * embedding.dartUnit d) =
    ((‖embedding.vertex d.snd - embedding.vertex d.fst‖ - 2 * r : ℝ) : ℂ) *
      embedding.dartUnit d
  calc
    _ = (embedding.vertex d.snd - embedding.vertex d.fst) -
        (2 * r : ℝ) * embedding.dartUnit d := by push_cast; ring
    _ = (‖embedding.vertex d.snd - embedding.vertex d.fst‖ : ℂ) *
          embedding.dartUnit d - (2 * r : ℝ) * embedding.dartUnit d := by
        exact congrArg (fun z : ℂ ↦
          z - (2 * r : ℝ) * embedding.dartUnit d)
            (embedding.dartVector_eq_norm_mul_dartUnit d)
    _ = _ := by push_cast; ring



theorem kwAngularPortVertex_matching_positive
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) {r : ℝ}
    {p q : KWDartPort G}
    (hmatching : kwDartOfPort G q = (kwDartOfPort G p).symm)
    (hr : 2 * r <
      ‖embedding.vertex (kwDartOfPort G p).snd -
        embedding.vertex (kwDartOfPort G p).fst‖) :
    ∃ c : ℝ, 0 < c ∧
      kwAngularPortVertex embedding r q - kwAngularPortVertex embedding r p =
        (c : ℂ) * embedding.dartUnit (kwDartOfPort G p) := by
  refine ⟨‖embedding.vertex (kwDartOfPort G p).snd -
      embedding.vertex (kwDartOfPort G p).fst‖ - 2 * r, by linarith, ?_⟩
  exact kwAngularPortVertex_matching_sub embedding r hmatching



theorem kwAngularPortVertex_eq_iff_dartUnit_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) {r : ℝ} (hr : r ≠ 0)
    {p q : KWDartPort G} (howner : p.1 = q.1) :
    kwAngularPortVertex embedding r p = kwAngularPortVertex embedding r q ↔
      embedding.dartUnit (kwDartOfPort G p) =
        embedding.dartUnit (kwDartOfPort G q) := by
  unfold kwAngularPortVertex
  rw [howner]
  constructor
  · intro h
    have hmul : (r : ℂ) * embedding.dartUnit (kwDartOfPort G p) =
        (r : ℂ) * embedding.dartUnit (kwDartOfPort G q) := by
      exact add_left_cancel h
    exact mul_left_cancel₀ (by exact_mod_cast hr) hmul
  · intro h
    rw [h]

theorem kwAngularPortVertex_ne_of_same_owner
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) {r : ℝ} (hr : r ≠ 0)
    {p q : KWDartPort G} (howner : p.1 = q.1) (hpq : p ≠ q) :
    kwAngularPortVertex embedding r p ≠
      kwAngularPortVertex embedding r q := by
  intro heq
  have hunit := (kwAngularPortVertex_eq_iff_dartUnit_eq
    embedding hr howner).mp heq
  exact embedding.dartUnit_ne_of_outgoing
    ((kwDartOfPort_fst G p).trans
      (howner.trans (kwDartOfPort_fst G q).symm))
    ((kwDartOfPort_injective G).ne hpq) hunit

theorem KWAngularPortRadiusData.portVertex_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (data : KWAngularPortRadiusData embedding) :
    Function.Injective (kwAngularPortVertex embedding (data.radius : ℝ)) := by
  intro p q heq
  by_cases howner : p.1 = q.1
  · by_contra hpq
    exact kwAngularPortVertex_ne_of_same_owner embedding
      (by exact_mod_cast data.radius_pos.ne') howner hpq heq
  · exfalso
    have hsep := data.vertex_separated p.1 q.1 howner
    have hp : dist (embedding.vertex p.1)
        (kwAngularPortVertex embedding (data.radius : ℝ) p) =
        (data.radius : ℝ) := by
      simpa only [_root_.dist_comm, abs_of_nonneg data.radius.coe_nonneg] using
        dist_kwAngularPortVertex_owner embedding (data.radius : ℝ) p
    have hq : dist (kwAngularPortVertex embedding (data.radius : ℝ) q)
        (embedding.vertex q.1) = (data.radius : ℝ) := by
      rw [dist_kwAngularPortVertex_owner]
      exact abs_of_nonneg data.radius.coe_nonneg
    have htriangle : dist (embedding.vertex p.1) (embedding.vertex q.1) ≤
        dist (embedding.vertex p.1)
            (kwAngularPortVertex embedding (data.radius : ℝ) p) +
          dist (kwAngularPortVertex embedding (data.radius : ℝ) p)
            (embedding.vertex q.1) := dist_triangle _ _ _
    rw [hp, heq, hq] at htriangle
    linarith [data.radius_pos]

theorem KWAngularPortRadiusData.portVertex_mem_sphere
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (data : KWAngularPortRadiusData embedding) (p : KWDartPort G) :
    kwAngularPortVertex embedding (data.radius : ℝ) p ∈
      Metric.sphere (embedding.vertex p.1) (data.radius : ℝ) := by
  rw [Metric.mem_sphere]
  simpa only [_root_.dist_comm, abs_of_nonneg data.radius.coe_nonneg] using
    dist_kwAngularPortVertex_owner embedding (data.radius : ℝ) p

private theorem kw_mem_openSegment_of_sbtw {a z b : ℂ}
    (hz : Sbtw ℝ a z b) : z ∈ openSegment ℝ a b := by
  rw [openSegment_eq_image_lineMap]
  exact (sbtw_iff_mem_image_Ioo_and_ne.mp hz).1



theorem KWAngularPortRadiusData.internalChord_mem_ball
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (data : KWAngularPortRadiusData embedding)
    {p q : KWDartPort G} (howner : p.1 = q.1) (hpq : p ≠ q)
    {z : ℂ}
    (hz : Sbtw ℝ
      (kwAngularPortVertex embedding (data.radius : ℝ) p) z
      (kwAngularPortVertex embedding (data.radius : ℝ) q)) :
    z ∈ Metric.ball (embedding.vertex p.1) (data.radius : ℝ) := by
  have hpclosed : kwAngularPortVertex embedding (data.radius : ℝ) p ∈
      Metric.closedBall (embedding.vertex p.1) (data.radius : ℝ) := by
    rw [Metric.mem_closedBall]
    exact le_of_eq (data.portVertex_mem_sphere p)
  have hqclosed : kwAngularPortVertex embedding (data.radius : ℝ) q ∈
      Metric.closedBall (embedding.vertex p.1) (data.radius : ℝ) := by
    rw [Metric.mem_closedBall]
    have hqdist : dist (kwAngularPortVertex embedding (data.radius : ℝ) q)
        (embedding.vertex q.1) = (data.radius : ℝ) :=
      data.portVertex_mem_sphere q
    rw [howner]
    exact le_of_eq hqdist
  apply openSegment_subset_ball_of_ne hpclosed hqclosed
    (data.portVertex_injective.ne hpq)
  exact kw_mem_openSegment_of_sbtw hz



theorem KWAngularPortRadiusData.internalChords_disjoint_of_owner_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {embedding : KWStraightLineEmbedding G}
    (data : KWAngularPortRadiusData embedding)
    {p q p' q' : KWDartPort G}
    (hpowner : p.1 = q.1) (hpq : p ≠ q)
    (hqowner : p'.1 = q'.1) (hpq' : p' ≠ q')
    (howners : p.1 ≠ p'.1) :
    Disjoint
      {z : ℂ | Sbtw ℝ
        (kwAngularPortVertex embedding (data.radius : ℝ) p) z
        (kwAngularPortVertex embedding (data.radius : ℝ) q)}
      {z : ℂ | Sbtw ℝ
        (kwAngularPortVertex embedding (data.radius : ℝ) p') z
        (kwAngularPortVertex embedding (data.radius : ℝ) q')} := by
  rw [Set.disjoint_left]
  intro z hz hz'
  have hball := data.internalChord_mem_ball hpowner hpq hz
  have hball' := data.internalChord_mem_ball hqowner hpq' hz'
  have hsep := data.vertex_separated p.1 p'.1 howners
  have htri : dist (embedding.vertex p.1) (embedding.vertex p'.1) ≤
      dist (embedding.vertex p.1) z + dist z (embedding.vertex p'.1) :=
    dist_triangle _ _ _
  have hzlt := Metric.mem_ball'.mp hball
  have hzlt' : dist z (embedding.vertex p'.1) < (data.radius : ℝ) := by
    simpa only [_root_.dist_comm] using Metric.mem_ball'.mp hball'
  linarith

end StatMech.FrontierA
