/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
























































import Code.Foundations.CylinderDeriv
import Code.Lattice.Clusters
import Code.Lattice.HypercubicLattice
import Code.Percolation.Theta

open MeasureTheory Function Set
open scoped NNReal ENNReal

namespace StatMech

namespace Percolation

open StatMech.Lattice








section Finite

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def w1 (p : ℝ≥0) (hp : p ≤ 1) (b : Bool) : ℝ := (bernoulliMeasure p hp).real {b}


theorem w1_sum (p : ℝ≥0) (hp : p ≤ 1) : (∑ b : Bool, w1 p hp b) = 1 := by
  have h : (∑ b : Bool, w1 p hp b) = (bernoulliMeasure p hp).real Set.univ := by
    simp only [w1]
    rw [← MeasureTheory.measureReal_biUnion_finset]
    · congr 1; ext x; simp
    · intro a _ b _ hab; simp only [Set.disjoint_singleton]; exact hab
    · intro a _; exact measurableSet_singleton a
  rw [h, probReal_univ]



noncomputable def W (p : ℝ≥0) (hp : p ≤ 1) (ω : ConfigSpace E) : ℝ := ∏ e, w1 p hp (ω e)


noncomputable def wsum (p : ℝ≥0) (hp : p ≤ 1) (f : ConfigSpace E → ℝ) : ℝ :=
  ∑ ω : ConfigSpace E, f ω * W p hp ω




theorem part_norm (p : ℝ≥0) (hp : p ≤ 1) (Sₜ : Type*) [Fintype Sₜ] [DecidableEq Sₜ] :
    (∑ x : Sₜ → Bool, ∏ i, w1 p hp (x i)) = 1 := by
  classical
  rw [← Fintype.prod_sum (fun (_ : Sₜ) (b : Bool) => w1 p hp b)]
  have h : ∀ _ : Sₜ, (∑ b : Bool, w1 p hp b) = 1 := fun _ => w1_sum p hp
  rw [Finset.prod_congr rfl (fun i _ => h i)]; simp





theorem wsum_mul (p : ℝ≥0) (hp : p ≤ 1) (P : E → Prop) [DecidablePred P]
    (f g : ConfigSpace E → ℝ)
    (hf : ∀ ω ω', (∀ e, P e → ω e = ω' e) → f ω = f ω')
    (hg : ∀ ω ω', (∀ e, ¬ P e → ω e = ω' e) → g ω = g ω') :
    wsum p hp (fun ω => f ω * g ω) = wsum p hp f * wsum p hp g := by
  classical
  set ee := Equiv.piEquivPiSubtypeProd P (fun _ : E => Bool) with hee
  have hsymm : ∀ (a : ∀ i : {x // P x}, Bool) (b : ∀ i : {x // ¬ P x}, Bool) (e : E),
      ee.symm (a, b) e = if h : P e then a ⟨e, h⟩ else b ⟨e, h⟩ := fun _ _ _ => rfl
  have hWfac : ∀ (a : ∀ i : {x // P x}, Bool) (b : ∀ i : {x // ¬ P x}, Bool),
      W p hp (ee.symm (a, b))
        = (∏ i : {x // P x}, w1 p hp (a i)) * (∏ i : {x // ¬ P x}, w1 p hp (b i)) := by
    intro a b
    unfold W
    rw [← Fintype.prod_subtype_mul_prod_subtype P (fun e => w1 p hp (ee.symm (a, b) e))]
    congr 1
    · exact Finset.prod_congr rfl (fun i _ => by rw [hsymm]; simp [i.2])
    · exact Finset.prod_congr rfl (fun i _ => by rw [hsymm]; simp [i.2])
  have hffac : ∀ (a : ∀ i : {x // P x}, Bool) (b : ∀ i : {x // ¬ P x}, Bool),
      f (ee.symm (a, b)) = f (ee.symm (a, fun _ => false)) :=
    fun a b => hf _ _ (fun e he => by rw [hsymm, hsymm]; simp [he])
  have hgfac : ∀ (a : ∀ i : {x // P x}, Bool) (b : ∀ i : {x // ¬ P x}, Bool),
      g (ee.symm (a, b)) = g (ee.symm (fun _ => false, b)) :=
    fun a b => hg _ _ (fun e he => by rw [hsymm, hsymm]; simp [he])
  have reidx : ∀ (φ : ConfigSpace E → ℝ),
      (∑ ω : ConfigSpace E, φ ω)
        = ∑ x : (∀ i : {x // P x}, Bool) × (∀ i : {x // ¬ P x}, Bool), φ (ee.symm x) :=
    fun φ => (Equiv.sum_comp ee.symm φ).symm
  unfold wsum
  rw [reidx (fun ω => (f ω * g ω) * W p hp ω), reidx (fun ω => f ω * W p hp ω),
      reidx (fun ω => g ω * W p hp ω)]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
  have lhs_eq :
      (∑ a, ∑ b, (f (ee.symm (a, b)) * g (ee.symm (a, b))) * W p hp (ee.symm (a, b)))
        = (∑ a, f (ee.symm (a, fun _ => false)) * (∏ i, w1 p hp (a i)))
          * (∑ b, g (ee.symm (fun _ => false, b)) * (∏ i, w1 p hp (b i))) := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [hWfac, hffac a b, hgfac a b]; ring
  have rhs1 :
      (∑ a, ∑ b, f (ee.symm (a, b)) * W p hp (ee.symm (a, b)))
        = ∑ a, f (ee.symm (a, fun _ => false)) * (∏ i, w1 p hp (a i)) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    have hstep : (∑ b, f (ee.symm (a, b)) * W p hp (ee.symm (a, b)))
        = f (ee.symm (a, fun _ => false)) * (∏ i, w1 p hp (a i))
          * (∑ b : (∀ i : {x // ¬ P x}, Bool), ∏ i, w1 p hp (b i)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun b _ => by rw [hWfac, hffac a b]; ring)
    rw [hstep, part_norm p hp]; ring
  have rhs2 :
      (∑ a, ∑ b, g (ee.symm (a, b)) * W p hp (ee.symm (a, b)))
        = ∑ b, g (ee.symm (fun _ => false, b)) * (∏ i, w1 p hp (b i)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    have hstep : (∑ a, g (ee.symm (a, b)) * W p hp (ee.symm (a, b)))
        = g (ee.symm (fun _ => false, b)) * (∏ i, w1 p hp (b i))
          * (∑ a : (∀ i : {x // P x}, Bool), ∏ i, w1 p hp (a i)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun a _ => by rw [hWfac, hgfac a b]; ring)
    rw [hstep, part_norm p hp]; ring
  rw [lhs_eq, rhs1, rhs2]



theorem real_eq_wsum (p : ℝ≥0) (hp : p ≤ 1) (A : Set (ConfigSpace E)) :
    (bernoulliProductMeasure (E := E) p hp).real A
      = wsum p hp (A.indicator (fun _ => (1 : ℝ))) := by
  classical
  rw [bernoulliProductMeasure.real_eq_sum A]
  unfold wsum W w1
  exact Finset.sum_congr rfl (fun ω _ => by rw [bernoulliProductMeasure.real_singleton ω])






theorem indep_cylinder (p : ℝ≥0) (hp : p ≤ 1) (P : E → Prop) [DecidablePred P]
    (A B : Set (ConfigSpace E))
    (hA : ∀ ω ω', (∀ e, P e → ω e = ω' e) → (ω ∈ A ↔ ω' ∈ A))
    (hB : ∀ ω ω', (∀ e, ¬ P e → ω e = ω' e) → (ω ∈ B ↔ ω' ∈ B)) :
    (bernoulliProductMeasure (E := E) p hp).real (A ∩ B)
      = (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B := by
  classical
  rw [real_eq_wsum, real_eq_wsum, real_eq_wsum]
  rw [show (A ∩ B).indicator (fun _ => (1 : ℝ))
        = fun ω => A.indicator (fun _ => (1:ℝ)) ω * B.indicator (fun _ => (1:ℝ)) ω from ?_]
  · apply wsum_mul p hp P
    · intro ω ω' hω
      by_cases hmem : ω ∈ A
      · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem ((hA ω ω' hω).mp hmem)]
      · rw [Set.indicator_of_notMem hmem,
          Set.indicator_of_notMem (fun hc => hmem ((hA ω ω' hω).mpr hc))]
    · intro ω ω' hω
      by_cases hmem : ω ∈ B
      · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem ((hB ω ω' hω).mp hmem)]
      · rw [Set.indicator_of_notMem hmem,
          Set.indicator_of_notMem (fun hc => hmem ((hB ω ω' hω).mpr hc))]
  · funext ω
    rw [← Set.inter_indicator_mul (fun _ => (1:ℝ)) (fun _ => (1:ℝ)) ω]; simp

end Finite








section Infinite

variable {E : Type*} [Countable E] [DecidableEq E]

omit [Countable E] [DecidableEq E] in

theorem indic_iff {X : Set (ConfigSpace E)} {a b : ConfigSpace E}
    (h : X.indicator (fun _ => (1:ℝ)) a = X.indicator (fun _ => (1:ℝ)) b) :
    (a ∈ X ↔ b ∈ X) := by
  by_cases ha : a ∈ X
  · rw [Set.indicator_of_mem ha] at h
    refine ⟨fun _ => ?_, fun _ => ha⟩
    by_contra hb; rw [Set.indicator_of_notMem hb] at h; norm_num at h
  · rw [Set.indicator_of_notMem ha] at h
    refine ⟨fun hc => absurd hc ha, fun hb => ?_⟩
    by_contra; rw [Set.indicator_of_mem hb] at h; norm_num at h










theorem indep_cylinder_inf (p : ℝ≥0) (hp : p ≤ 1)
    (A B : Set (ConfigSpace E)) (T U : Finset E) (hdisj : Disjoint T U)
    (hA : DependsOn (A.indicator (fun _ => (1 : ℝ))) (T : Set E))
    (hB : DependsOn (B.indicator (fun _ => (1 : ℝ))) (U : Set E)) :
    (bernoulliProductMeasure (E := E) p hp).real (A ∩ B)
      = (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B := by
  classical
  set F := T ∪ U with hF
  have hAF : DependsOn (A.indicator (fun _ => (1 : ℝ))) (F : Set E) := hA.mono (by simp [hF])
  have hBF : DependsOn (B.indicator (fun _ => (1 : ℝ))) (F : Set E) := hB.mono (by simp [hF])
  have hcylA : A = cylinder F (F.restrict '' A) := eq_cylinder_restrict_image A F hAF
  have hcylB : B = cylinder F (F.restrict '' B) := eq_cylinder_restrict_image B F hBF
  
  have hmemA : ∀ (η : ConfigSpace ↥F),
      (η ∈ F.restrict '' A ↔ extendOff F (fun _ => false) η ∈ A) := by
    intro η
    refine ⟨fun hη => ?_, fun hext => ?_⟩
    · rw [hcylA, mem_cylinder, restrict_extendOff]; exact hη
    · have hc : extendOff F (fun _ => false) η ∈ cylinder F (F.restrict '' A) := hcylA ▸ hext
      rw [mem_cylinder, restrict_extendOff] at hc; exact hc
  have hmemB : ∀ (η : ConfigSpace ↥F),
      (η ∈ F.restrict '' B ↔ extendOff F (fun _ => false) η ∈ B) := by
    intro η
    refine ⟨fun hη => ?_, fun hext => ?_⟩
    · rw [hcylB, mem_cylinder, restrict_extendOff]; exact hη
    · have hc : extendOff F (fun _ => false) η ∈ cylinder F (F.restrict '' B) := hcylB ▸ hext
      rw [mem_cylinder, restrict_extendOff] at hc; exact hc
  
  have hAagree : ∀ η η' : ConfigSpace ↥F,
      (∀ j : ↥F, (j : E) ∈ T → η j = η' j) → (η ∈ F.restrict '' A ↔ η' ∈ F.restrict '' A) := by
    intro η η' hagr
    rw [hmemA, hmemA]
    refine indic_iff (hA (fun e heT => ?_))
    have heT' : e ∈ T := heT
    have heF : e ∈ F := Finset.mem_union.mpr (Or.inl heT')
    simp only [extendOff, heF, dif_pos]; exact hagr ⟨e, heF⟩ heT'
  have hBagree : ∀ η η' : ConfigSpace ↥F,
      (∀ j : ↥F, ¬ ((j : E) ∈ T) → η j = η' j) → (η ∈ F.restrict '' B ↔ η' ∈ F.restrict '' B) := by
    intro η η' hagr
    rw [hmemB, hmemB]
    refine indic_iff (hB (fun e heU => ?_))
    have heU' : e ∈ U := heU
    have heF : e ∈ F := Finset.mem_union.mpr (Or.inr heU')
    have heT : ¬ (e ∈ T) := fun hc => Finset.disjoint_left.mp hdisj hc heU'
    simp only [extendOff, heF, dif_pos]; exact hagr ⟨e, heF⟩ heT
  
  have hPA : (bernoulliProductMeasure (E := E) p hp).real A
      = (bernoulliProductMeasure (E := ↥F) p hp).real (F.restrict '' A) := by
    conv_lhs => rw [hcylA]; rw [realProb_cylinder]
  have hPB : (bernoulliProductMeasure (E := E) p hp).real B
      = (bernoulliProductMeasure (E := ↥F) p hp).real (F.restrict '' B) := by
    conv_lhs => rw [hcylB]; rw [realProb_cylinder]
  have hPAB : (bernoulliProductMeasure (E := E) p hp).real (A ∩ B)
      = (bernoulliProductMeasure (E := ↥F) p hp).real ((F.restrict '' A) ∩ (F.restrict '' B)) := by
    conv_lhs => rw [hcylA, hcylB, inter_cylinder_same]; rw [realProb_cylinder]
  rw [hPA, hPB, hPAB]
  exact indep_cylinder p hp (fun j : ↥F => (j : E) ∈ T)
    (F.restrict '' A) (F.restrict '' B) hAagree hBagree

end Infinite








variable {d : ℕ}



def clusterWithin (d : ℕ) (ω : ConfigSpace (Sym2 (Site d))) (S : Set (Site d)) (o : Site d) :
    Set (Site d) :=
  {y | ∃ (hy : y ∈ S) (ho : o ∈ S), ConnectedWithin d ω S ⟨o, ho⟩ ⟨y, hy⟩}




def incidentWithin (K S : Set (Site d)) : Set (Sym2 (Site d)) :=
  {e | ∃ x ∈ K, ∃ y ∈ S, e = s(x, y)}

theorem mem_incidentWithin {K S : Set (Site d)} {x y : Site d} (hx : x ∈ K) (hy : y ∈ S) :
    s(x, y) ∈ incidentWithin K S := ⟨x, hx, y, hy, rfl⟩



theorem agree_KS {K S : Set (Site d)} {ω ω' : ConfigSpace (Sym2 (Site d))}
    (hagree : ∀ e ∈ incidentWithin K S, ω e = ω' e)
    {x y : Site d} (hx : x ∈ K) (hy : y ∈ S) :
    ω s(x, y) = ω' s(x, y) :=
  hagree _ (mem_incidentWithin hx hy)



theorem isOpenEdge_transfer {K S : Set (Site d)} {ω ω' : ConfigSpace (Sym2 (Site d))}
    (hagree : ∀ e ∈ incidentWithin K S, ω e = ω' e)
    {x y : Site d} (hx : x ∈ K) (hy : y ∈ S)
    (h : IsOpenEdge d ω x y) : IsOpenEdge d ω' x y := by
  obtain ⟨hadj, hopen⟩ := h
  exact ⟨hadj, by rw [← agree_KS hagree hx hy]; exact hopen⟩



theorem clusterWithin_closed {ω : ConfigSpace (Sym2 (Site d))} {S : Set (Site d)} {o : Site d}
    {x y : Site d} (hx : x ∈ clusterWithin d ω S o)
    (hyS : y ∈ S) (hopen : IsOpenEdge d ω x y) :
    y ∈ clusterWithin d ω S o := by
  obtain ⟨hxS, hoS, hconn⟩ := hx
  exact ⟨hyS, hoS, hconn.trans (SimpleGraph.Adj.reachable (show IsOpenEdge d ω x y from hopen))⟩





theorem walk_transfer {ω ω' : ConfigSpace (Sym2 (Site d))} {S : Set (Site d)} {o : Site d}
    (hagree : ∀ e ∈ incidentWithin (clusterWithin d ω S o) S, ω e = ω' e)
    {a b : ↥S} (w : (openSubgraphInduce d ω S).Walk a b)
    (ha : (a : Site d) ∈ clusterWithin d ω S o) :
    (b : Site d) ∈ clusterWithin d ω S o ∧
      Nonempty ((openSubgraphInduce d ω' S).Walk a b) := by
  induction w with
  | nil => exact ⟨ha, ⟨SimpleGraph.Walk.nil⟩⟩
  | @cons u v t hadj p ih =>
    have hopen : IsOpenEdge d ω (u : Site d) (v : Site d) := hadj
    have hvK : (v : Site d) ∈ clusterWithin d ω S o := clusterWithin_closed ha v.2 hopen
    obtain ⟨hbK, ⟨w'⟩⟩ := ih hvK
    have hopen' : IsOpenEdge d ω' (u : Site d) (v : Site d) :=
      isOpenEdge_transfer hagree ha v.2 hopen
    exact ⟨hbK, ⟨SimpleGraph.Walk.cons (show (openSubgraphInduce d ω' S).Adj u v from hopen') w'⟩⟩




theorem K_closed_omega' {ω ω' : ConfigSpace (Sym2 (Site d))} {S : Set (Site d)} {o : Site d}
    (hagree : ∀ e ∈ incidentWithin (clusterWithin d ω S o) S, ω e = ω' e)
    {x y : Site d} (hxK : x ∈ clusterWithin d ω S o) (hyS : y ∈ S)
    (hopen' : IsOpenEdge d ω' x y) : y ∈ clusterWithin d ω S o := by
  have hopen : IsOpenEdge d ω x y := by
    obtain ⟨hadj, ho'⟩ := hopen'
    exact ⟨hadj, by rw [agree_KS hagree hxK hyS]; exact ho'⟩
  exact clusterWithin_closed hxK hyS hopen



theorem walk_trap_omega' {ω ω' : ConfigSpace (Sym2 (Site d))} {S : Set (Site d)} {o : Site d}
    (hagree : ∀ e ∈ incidentWithin (clusterWithin d ω S o) S, ω e = ω' e)
    {a b : ↥S} (w : (openSubgraphInduce d ω' S).Walk a b)
    (ha : (a : Site d) ∈ clusterWithin d ω S o) :
    (b : Site d) ∈ clusterWithin d ω S o := by
  induction w with
  | nil => exact ha
  | @cons u v t hadj p ih =>
    have hopen' : IsOpenEdge d ω' (u : Site d) (v : Site d) := hadj
    exact ih (K_closed_omega' hagree ha v.2 hopen')






theorem clusterWithin_congr {ω ω' : ConfigSpace (Sym2 (Site d))} {S : Set (Site d)} {o : Site d}
    (hoS : o ∈ S)
    (hagree : ∀ e ∈ incidentWithin (clusterWithin d ω S o) S, ω e = ω' e) :
    clusterWithin d ω' S o = clusterWithin d ω S o := by
  have hoK : o ∈ clusterWithin d ω S o :=
    ⟨hoS, hoS, connectedWithin_refl ω S ⟨o, hoS⟩⟩
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro y ⟨_, _, hconn'⟩
    obtain ⟨w⟩ := hconn'
    exact walk_trap_omega' hagree w hoK
  · rintro y ⟨hyS, hoS', hconn⟩
    obtain ⟨w⟩ := hconn
    obtain ⟨_, ⟨w'⟩⟩ := walk_transfer hagree w hoK
    exact ⟨hyS, hoS', ⟨w'⟩⟩





def clusterEvent (d : ℕ) (S : Set (Site d)) (o : Site d) (K : Set (Site d)) :
    Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | clusterWithin d ω S o = K}



theorem clusterEvent_congr {S : Set (Site d)} {o : Site d} {K : Set (Site d)} (hoS : o ∈ S)
    {ω ω' : ConfigSpace (Sym2 (Site d))}
    (hagree : ∀ e ∈ incidentWithin K S, ω e = ω' e)
    (hω : ω ∈ clusterEvent d S o K) : ω' ∈ clusterEvent d S o K := by
  have hK : clusterWithin d ω S o = K := hω
  have hagree' : ∀ e ∈ incidentWithin (clusterWithin d ω S o) S, ω e = ω' e := by
    rw [hK]; exact hagree
  show clusterWithin d ω' S o = K
  rw [clusterWithin_congr hoS hagree', hK]

theorem clusterEvent_iff {S : Set (Site d)} {o : Site d} {K : Set (Site d)} (hoS : o ∈ S)
    {ω ω' : ConfigSpace (Sym2 (Site d))}
    (hagree : ∀ e ∈ incidentWithin K S, ω e = ω' e) :
    ω ∈ clusterEvent d S o K ↔ ω' ∈ clusterEvent d S o K :=
  ⟨clusterEvent_congr hoS hagree,
   clusterEvent_congr hoS (fun e he => (hagree e he).symm)⟩




def incidentWithinFinset (K S : Finset (Site d)) : Finset (Sym2 (Site d)) :=
  (K ×ˢ S).image (fun p => s(p.1, p.2))

theorem mem_incidentWithinFinset {K S : Finset (Site d)} {e : Sym2 (Site d)} :
    e ∈ incidentWithinFinset K S ↔ ∃ x ∈ K, ∃ y ∈ S, e = s(x, y) := by
  simp only [incidentWithinFinset, Finset.mem_image, Finset.mem_product]
  constructor
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, he⟩; exact ⟨x, hx, y, hy, he.symm⟩
  · rintro ⟨x, hx, y, hy, rfl⟩; exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩


theorem incidentWithinFinset_coe (K S : Finset (Site d)) :
    (incidentWithinFinset K S : Set (Sym2 (Site d)))
      = incidentWithin (K : Set _) (S : Set _) := by
  ext e
  rw [Finset.mem_coe, mem_incidentWithinFinset]
  simp only [incidentWithin, Set.mem_setOf_eq, Finset.mem_coe]




theorem clusterEvent_dependsOn {S : Finset (Site d)} {o : Site d} {K : Finset (Site d)}
    (hoS : o ∈ (S : Set (Site d))) :
    DependsOn ((clusterEvent d (S : Set (Site d)) o (K : Set (Site d))).indicator
      (fun _ => (1 : ℝ))) (incidentWithinFinset K S : Set (Sym2 (Site d))) := by
  intro ω ω' h
  rw [incidentWithinFinset_coe] at h
  have hiff := clusterEvent_iff (K := (K : Set (Site d))) hoS (fun e he => h e he)
  by_cases hω : ω ∈ clusterEvent d (S : Set (Site d)) o (K : Set (Site d))
  · rw [Set.indicator_of_mem hω, Set.indicator_of_mem (hiff.mp hω)]
  · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem (fun hc => hω (hiff.mpr hc))]













theorem exploration_decomposition (p : ℝ≥0) (hp : p ≤ 1)
    (S : Finset (Site d)) (o : Site d) (hoS : o ∈ (S : Set (Site d))) (K : Finset (Site d))
    (B : Set (ConfigSpace (Sym2 (Site d)))) (U : Finset (Sym2 (Site d)))
    (hdisj : Disjoint (incidentWithinFinset K S) U)
    (hB : DependsOn (B.indicator (fun _ => (1 : ℝ))) (U : Set (Sym2 (Site d)))) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
        (clusterEvent d (S : Set (Site d)) o (K : Set (Site d)) ∩ B)
      = (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          (clusterEvent d (S : Set (Site d)) o (K : Set (Site d)))
        * (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real B :=
  indep_cylinder_inf p hp _ B (incidentWithinFinset K S) U hdisj
    (clusterEvent_dependsOn hoS) hB

end Percolation

end StatMech
