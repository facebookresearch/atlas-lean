/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.Inequalities.Pivotal
import Code.Inequalities.ReimerButterfly
import Code.Inequalities.ReimerFiberClose
import Code.FK.RussoDerivativeBetaSum
import Code.Sharpness.BkCriterionInhom

open Finset SimpleGraph Set

namespace StatMech
namespace Sharpness

open ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]


def mpiCrossingEvent (o : V) (B : Set V) : Set (ConfigSpace (Sym2 V)) :=
  connEvent G Set.univ o B


noncomputable def mpiBlockedSet (B : Set V) (omega : ConfigSpace (Sym2 V)) : Finset V :=
  by
    classical
    exact Finset.univ.filter fun x => ¬ ConnToSet G omega Set.univ x B


def mpiSurfaceEvent (B : Set V) (S : Finset V) : Set (ConfigSpace (Sym2 V)) :=
  {omega | mpiBlockedSet G B omega = S}

theorem mpi_mem_blockedSet_iff (B : Set V) (omega : ConfigSpace (Sym2 V)) (x : V) :
    x ∈ mpiBlockedSet G B omega ↔ ¬ ConnToSet G omega Set.univ x B := by
  classical
  simp [mpiBlockedSet]

theorem mpi_not_mem_blockedSet_iff (B : Set V) (omega : ConfigSpace (Sym2 V)) (x : V) :
    x ∉ mpiBlockedSet G B omega ↔ ConnToSet G omega Set.univ x B := by
  rw [← not_iff_not]
  simp only [not_not, mpi_mem_blockedSet_iff]

theorem mpi_not_crossing_iff_mem_blockedSet (o : V) (B : Set V)
    (omega : ConfigSpace (Sym2 V)) :
    omega ∉ mpiCrossingEvent G o B ↔ o ∈ mpiBlockedSet G B omega := by
  rw [mpi_mem_blockedSet_iff]
  rfl


theorem mpi_connToSet_of_adj (B : Set V) (omega : ConfigSpace (Sym2 V))
    {x y : V} (hxy : G.Adj x y) (hopen : omega s(x, y) = true)
    (hy : ConnToSet G omega Set.univ y B) :
    ConnToSet G omega Set.univ x B := by
  obtain ⟨_, b, _, hbB, hyb⟩ := hy
  refine ⟨Set.mem_univ x, b, Set.mem_univ b, hbB, ?_⟩
  have hxy' : ((openSub G omega).induce Set.univ).Adj
      ⟨x, Set.mem_univ x⟩ ⟨y, Set.mem_univ y⟩ := by
    exact ⟨hxy, hopen⟩
  exact hxy'.reachable.trans hyb


theorem mpi_boundary_edge_closed (B : Set V) (omega : ConfigSpace (Sym2 V))
    {S : Finset V} (hS : mpiBlockedSet G B omega = S)
    {x y : V} (hx : x ∈ S) (hy : y ∉ S) (hxy : G.Adj x y) :
    omega s(x, y) = false := by
  have hxb : x ∈ mpiBlockedSet G B omega := hS.symm ▸ hx
  have hyb : y ∉ mpiBlockedSet G B omega := by simpa [hS] using hy
  have hxnot := (mpi_mem_blockedSet_iff G B omega x).mp hxb
  have hyconn := (mpi_not_mem_blockedSet_iff G B omega y).mp hyb
  cases hopen : omega s(x, y) with
  | false => rfl
  | true => exact False.elim (hxnot (mpi_connToSet_of_adj G B omega hxy hopen hyconn))


theorem mpi_le_setOpen (e : Sym2 V) (omega : ConfigSpace (Sym2 V)) :
    omega ≤ setOpen e omega := by
  intro j
  by_cases hje : j = e
  · subst j
    rw [setOpen_self]
    exact Bool.le_true _
  · rw [setOpen_of_ne hje]





theorem mpi_boundary_edge_isPivotal (o : V) (B : Set V)
    (omega : ConfigSpace (Sym2 V)) {S : Finset V}
    (hS : mpiBlockedSet G B omega = S) (ho : o ∈ S)
    {x y : V} (hx : x ∈ S) (hy : y ∉ S) (hxy : G.Adj x y)
    (hox : ConnToSet G omega (S : Set V) o {x}) :
    IsPivotal s(x, y) (mpiCrossingEvent G o B) omega := by
  let e : Sym2 V := s(x, y)
  have hclosed : omega e = false := mpi_boundary_edge_closed G B omega hS hx hy hxy
  have hclosedCfg : setClosed e omega = omega := by
    funext j
    by_cases hje : j = e
    · subst j
      simpa [hclosed] using setClosed_self e omega
    · exact setClosed_of_ne hje omega
  have hnot : setClosed e omega ∉ mpiCrossingEvent G o B := by
    rw [hclosedCfg, mpi_not_crossing_iff_mem_blockedSet]
    simpa [hS] using ho
  have hopenCfg : setOpen e omega ∈ mpiCrossingEvent G o B := by
    have hmono : ConnToSet G (setOpen e omega) (S : Set V) o {x} := by
      obtain ⟨hoS, z, hzS, hz, hconn⟩ := hox
      exact ⟨hoS, z, hzS, hz,
        hconn.mono_config G (mpi_le_setOpen e omega)⟩
    obtain ⟨z, _, hz, p, hpS⟩ := shk_walk_of_connToSet G (setOpen e omega)
      (S : Set V) o {x} hmono
    simp only [Set.mem_singleton_iff] at hz
    subst z
    have hyconn0 : ConnToSet G omega Set.univ y B := by
      apply (mpi_not_mem_blockedSet_iff G B omega y).mp
      simpa [hS] using hy
    have hyconn : ConnToSet G (setOpen e omega) Set.univ y B := by
      obtain ⟨hyU, b, hbU, hbB, hconn⟩ := hyconn0
      exact ⟨hyU, b, hbU, hbB,
        hconn.mono_config G (mpi_le_setOpen e omega)⟩
    obtain ⟨b, _, hbB, q, _⟩ := shk_walk_of_connToSet G (setOpen e omega)
      Set.univ y B hyconn
    have hxyOpen : (openSub G (setOpen e omega)).Adj x y := by
      exact ⟨hxy, by simp [e]⟩
    let walk : (openSub G (setOpen e omega)).Walk o b :=
      p.append (SimpleGraph.Walk.cons hxyOpen q)
    refine ⟨Set.mem_univ o, b, Set.mem_univ b, hbB, ?_⟩
    exact ⟨walk.induce Set.univ (fun _ _ => Set.mem_univ _)⟩
  exact (isPivotal_iff_of_isIncreasing
    (isIncreasing_connEvent G Set.univ o B) omega).2 ⟨hnot, hopenCfg⟩




def mpiInternalEdges (S : Set V) : Set (Sym2 V) :=
  {e | ∃ x ∈ S, ∃ y ∈ S, e = s(x, y)}

theorem mpi_internalEdge_mk {S : Set V} {x y : V} (hx : x ∈ S) (hy : y ∈ S) :
    s(x, y) ∈ mpiInternalEdges S := ⟨x, hx, y, hy, rfl⟩

theorem mpi_not_internalEdge_mk_of_right {S : Set V} {x y : V} (hy : y ∉ S) :
    s(x, y) ∉ mpiInternalEdges S := by
  rintro ⟨a, ha, b, hb, hab⟩
  rw [Sym2.eq_iff] at hab
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hy hb
  · exact hy ha


theorem mpi_connWithin_transfer {omega omega' : ConfigSpace (Sym2 V)} {S : Set V}
    (hagree : ∀ e ∈ mpiInternalEdges S, omega e = omega' e)
    {a b : S} (h : ConnWithin G omega S a b) : ConnWithin G omega' S a b := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons u v t hadj p ih =>
      have hopen' : (openSub G omega').Adj (u : V) (v : V) := by
        refine ⟨hadj.1, ?_⟩
        rw [← hagree s((u : V), (v : V))
          (mpi_internalEdge_mk (S := S) u.2 v.2)]
        exact hadj.2
      exact (show ((openSub G omega').induce S).Adj u v from hopen').reachable.trans ih


theorem mpi_connEvent_determined_internal (S : Finset V) (o x : V) :
    DeterminedBy (connEvent G (S : Set V) o {x}) (mpiInternalEdges (S : Set V)) := by
  intro omega omega' hagree
  constructor
  · rintro ⟨ho, z, hzS, hz, hconn⟩
    exact ⟨ho, z, hzS, hz,
      mpi_connWithin_transfer (omega := omega) (omega' := omega') G
        (fun e he => (hagree e he).symm) hconn⟩
  · rintro ⟨ho, z, hzS, hz, hconn⟩
    exact ⟨ho, z, hzS, hz,
      mpi_connWithin_transfer (omega := omega') (omega' := omega) G
        (fun e he => hagree e he) hconn⟩



theorem mpi_connEventSet_determined_internal (S : Finset V) (o : V) (B : Set V) :
    DeterminedBy (connEvent G (S : Set V) o B) (mpiInternalEdges (S : Set V)) := by
  intro omega omega' hagree
  constructor
  · rintro ⟨ho, z, hzS, hzB, hconn⟩
    exact ⟨ho, z, hzS, hzB,
      mpi_connWithin_transfer (omega := omega) (omega' := omega') G
        (fun e he => (hagree e he).symm) hconn⟩
  · rintro ⟨ho, z, hzS, hzB, hconn⟩
    exact ⟨ho, z, hzS, hzB,
      mpi_connWithin_transfer (omega := omega') (omega' := omega) G
        (fun e he => hagree e he) hconn⟩


theorem mpi_target_not_mem_blockedSet (B : Set V) (omega : ConfigSpace (Sym2 V))
    {b : V} (hb : b ∈ B) : b ∉ mpiBlockedSet G B omega := by
  rw [mpi_not_mem_blockedSet_iff]
  exact ⟨Set.mem_univ b, b, Set.mem_univ b, hb, SimpleGraph.Reachable.refl _⟩


theorem mpi_surfaceEvent_nonempty_disjoint (B : Set V) (S : Finset V)
    (hocc : (mpiSurfaceEvent G B S).Nonempty) :
    Disjoint (S : Set V) B := by
  rw [Set.disjoint_left]
  intro x hxS hxB
  obtain ⟨omega, homega⟩ := hocc
  have hxblocked : x ∈ mpiBlockedSet G B omega := by
    rw [homega]
    exact hxS
  exact mpi_target_not_mem_blockedSet G B omega hxB hxblocked



theorem mpi_outside_connection_walk (B : Set V) (omega : ConfigSpace (Sym2 V))
    {S : Finset V} (hS : mpiBlockedSet G B omega = S) {y : V} (hy : y ∉ S) :
    ∃ b ∈ B, ∃ p : (openSub G omega).Walk y b,
      ∀ z ∈ p.support, z ∉ S := by
  have hyconn : ConnToSet G omega Set.univ y B := by
    apply (mpi_not_mem_blockedSet_iff G B omega y).mp
    simpa [hS] using hy
  obtain ⟨b, _, hbB, p, _⟩ := shk_walk_of_connToSet G omega Set.univ y B hyconn
  refine ⟨b, hbB, p, ?_⟩
  intro z hz hzS
  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hz
  obtain ⟨i, hiz, hi⟩ := hz
  let q : (openSub G omega).Walk z b := (p.drop i).copy hiz rfl
  have hzconn : ConnToSet G omega Set.univ z B := by
    refine ⟨Set.mem_univ z, b, Set.mem_univ b, hbB, ?_⟩
    exact ⟨q.induce Set.univ (fun _ _ => Set.mem_univ _)⟩
  have hzb : z ∈ mpiBlockedSet G B omega := by simpa [hS] using hzS
  exact (mpi_mem_blockedSet_iff G B omega z).mp hzb hzconn



theorem mpi_outside_conn_transfer {B : Set V} {S : Finset V}
    {omega omega' : ConfigSpace (Sym2 V)}
    (hS : mpiBlockedSet G B omega = S)
    (hagree : agreeOn (mpiInternalEdges (S : Set V))ᶜ omega omega')
    {y : V} (hy : y ∉ S) : ConnToSet G omega' Set.univ y B := by
  obtain ⟨b, hbB, p, hpout⟩ := mpi_outside_connection_walk G B omega hS hy
  have hpAgree : agreeOn {e : Sym2 V | e ∈ p.edges} omega omega' := by
    intro e he
    apply hagree
    induction e using Sym2.ind with
    | _ a c =>
        exact mpi_not_internalEdge_mk_of_right
          (hpout c (p.snd_mem_support_of_mem_edges he))
  let q : (openSub G omega').Walk y b :=
    p.transfer (openSub G omega') (shk_edges_subset_openSub G omega omega' p hpAgree)
  refine ⟨Set.mem_univ y, b, Set.mem_univ b, hbB, ?_⟩
  exact ⟨q.induce Set.univ (fun _ _ => Set.mem_univ _)⟩



theorem mpi_inside_not_conn_of_exterior_agree {B : Set V} {S : Finset V}
    {omega omega' : ConfigSpace (Sym2 V)}
    (hS : mpiBlockedSet G B omega = S)
    (hagree : agreeOn (mpiInternalEdges (S : Set V))ᶜ omega omega')
    {x : V} (hx : x ∈ S) : ¬ ConnToSet G omega' Set.univ x B := by
  intro hxconn
  obtain ⟨b, _, hbB, p, _⟩ := shk_walk_of_connToSet G omega' Set.univ x B hxconn
  have hbS : b ∉ (S : Set V) := by
    intro hbSin
    have hbb : b ∈ mpiBlockedSet G B omega := by simpa [hS] using hbSin
    exact (mpi_target_not_mem_blockedSet G B omega hbB) hbb
  obtain ⟨a, y, haS, hyS, hay, htriple⟩ :=
    shk_firstExit_triple G omega' Set.univ (S : Set V) B x b
      (by exact_mod_cast hx) hbB hbS p.bypass p.bypass_isPath (fun _ _ => Set.mem_univ _)
  have hinter := disjointOccurrence_subset_inter _ _ htriple
  have hinner := disjointOccurrence_subset_inter _ _ hinter.2
  have hopen' : omega' s(a, y) = true := hinner.1
  have hopen : omega s(a, y) = true := by
    exact (hagree s(a, y) (mpi_not_internalEdge_mk_of_right hyS)).symm.trans hopen'
  have hyconn : ConnToSet G omega Set.univ y B := by
    apply (mpi_not_mem_blockedSet_iff G B omega y).mp
    simpa [hS] using hyS
  have haconn := mpi_connToSet_of_adj G B omega hay hopen hyconn
  have hablocked : a ∈ mpiBlockedSet G B omega := by simpa [hS] using haS
  exact (mpi_mem_blockedSet_iff G B omega a).mp hablocked haconn


theorem mpi_surfaceEvent_determined_exterior (B : Set V) (S : Finset V) :
    DeterminedBy (mpiSurfaceEvent G B S) (mpiInternalEdges (S : Set V))ᶜ := by
  intro omega omega' hagree
  have transfer : ∀ {eta eta' : ConfigSpace (Sym2 V)},
      agreeOn (mpiInternalEdges (S : Set V))ᶜ eta eta' →
      mpiBlockedSet G B eta = S → mpiBlockedSet G B eta' = S := by
    intro eta eta' hagree' hsurf
    ext z
    rw [mpi_mem_blockedSet_iff]
    change (¬ ConnToSet G eta' Set.univ z B) ↔ z ∈ S
    constructor
    · intro hznot
      by_contra hzS
      have hzconn : ConnToSet G eta' Set.univ z B :=
        mpi_outside_conn_transfer G hsurf hagree' hzS
      exact hznot hzconn
    · intro hzS
      exact mpi_inside_not_conn_of_exterior_agree G hsurf hagree' hzS
  constructor
  · exact transfer hagree
  · exact transfer (fun e he => (hagree e he).symm)



theorem mpi_conn_surface_factor (beta : ℝ) (J : Sym2 V → ℝ)
    (B : Set V) (S : Finset V) (o x : V) :
    wprob (shk_edgeLaw beta J)
        (connEvent G (S : Set V) o {x} ∩ mpiSurfaceEvent G B S) =
      wprob (shk_edgeLaw beta J) (connEvent G (S : Set V) o {x}) *
        wprob (shk_edgeLaw beta J) (mpiSurfaceEvent G B S) := by
  exact wprob_inter_eq_mul_of_determined _ _ disjoint_compl_right
    (shk_edgeLaw beta J) (shk_edgeLaw_sum_one beta J)
    (mpi_connEvent_determined_internal G S o x)
    (mpi_surfaceEvent_determined_exterior G B S)




noncomputable def mpiPhi (beta : ℝ) (J : Sym2 V → ℝ)
    (o : V) (S : Finset V) : ℝ :=
  ∑ q ∈ shk_boundaryPairs G S,
    (1 - Real.exp (-beta * J s(q.1, q.2))) *
      wprob (shk_edgeLaw beta J) (connEvent G (S : Set V) o {q.1})



theorem mpi_wprob_crossing_compl_eq_sum_surfaces
    (phi : Sym2 V → Bool → ℝ) (hphi : ∀ e, phi e false + phi e true = 1)
    (o : V) (B : Set V) :
    wprob phi (mpiCrossingEvent G o B)ᶜ =
      ∑ S ∈ (Finset.univ.filter fun S : Finset V => o ∈ S),
        wprob phi (mpiSurfaceEvent G B S) := by
  classical
  unfold wprob
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro omega _
  by_cases hcross : omega ∈ mpiCrossingEvent G o B
  · rw [Set.indicator_of_notMem (by simpa using hcross)]
    rw [zero_mul]
    symm
    apply Finset.sum_eq_zero
    intro S hS
    rw [Set.indicator_of_notMem]
    · exact zero_mul _
    · intro hsurf
      have hoS : o ∈ S := (Finset.mem_filter.mp hS).2
      have hblocked : mpiBlockedSet G B omega = S := hsurf
      have hob : o ∈ mpiBlockedSet G B omega := hblocked.symm ▸ hoS
      exact (mpi_not_crossing_iff_mem_blockedSet G o B omega).mpr hob hcross
  · rw [Set.indicator_of_mem (by simpa using hcross), one_mul]
    let S0 := mpiBlockedSet G B omega
    have hoS0 : o ∈ S0 := (mpi_not_crossing_iff_mem_blockedSet G o B omega).mp hcross
    have hS0mem : S0 ∈ (Finset.univ.filter fun S : Finset V => o ∈ S) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hoS0⟩
    symm
    calc
      (∑ S ∈ (Finset.univ.filter fun S : Finset V => o ∈ S),
          (mpiSurfaceEvent G B S).indicator (fun _ => (1 : ℝ)) omega *
            pweight phi omega) =
          (mpiSurfaceEvent G B S0).indicator (fun _ => (1 : ℝ)) omega *
            pweight phi omega := by
        apply Finset.sum_eq_single S0
        · intro S hSmem hSne
          rw [Set.indicator_of_notMem]
          · exact zero_mul _
          · exact fun heq => hSne heq.symm
        · exact fun hnot => False.elim (hnot hS0mem)
      _ = pweight phi omega := by
        rw [Set.indicator_of_mem (show omega ∈ mpiSurfaceEvent G B S0 from rfl), one_mul]


theorem mpi_wprob_compl (phi : Sym2 V → Bool → ℝ)
    (hphi : ∀ e, phi e false + phi e true = 1)
    (A : Set (ConfigSpace (Sym2 V))) :
    wprob phi Aᶜ = 1 - wprob phi A := by
  have h := wprob_add_compl phi hphi A
  linarith



theorem mpi_perSurface_eq_phi (beta : ℝ) (J : Sym2 V → ℝ)
    (o : V) (B : Set V) (S : Finset V) :
    (∑ q ∈ shk_boundaryPairs G S,
      (1 - Real.exp (-beta * J s(q.1, q.2))) *
        wprob (shk_edgeLaw beta J)
          (connEvent G (S : Set V) o {q.1} ∩ mpiSurfaceEvent G B S)) =
      mpiPhi G beta J o S * wprob (shk_edgeLaw beta J) (mpiSurfaceEvent G B S) := by
  unfold mpiPhi
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q _
  rw [mpi_conn_surface_factor G beta J B S o q.1]
  ring



theorem mpi_openWeight_div_beta_le (beta Je : ℝ)
    (hbeta : 0 < beta) (hJe : 0 ≤ Je) :
    (1 / beta) * (1 - Real.exp (-beta * Je)) ≤ Je := by
  have ht := Real.add_one_le_exp (-beta * Je)
  have hp : 1 - Real.exp (-beta * Je) ≤ beta * Je := by linarith
  rw [one_div, inv_mul_le_iff₀ hbeta]
  simpa [mul_comm] using hp



theorem mpi_phi_surface_le_boundaryJ (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 < beta) (hJ : ∀ e, 0 ≤ J e)
    (o : V) (B : Set V) (S : Finset V) :
    (1 / beta) * mpiPhi G beta J o S *
        wprob (shk_edgeLaw beta J) (mpiSurfaceEvent G B S) ≤
      ∑ q ∈ shk_boundaryPairs G S,
        J s(q.1, q.2) * wprob (shk_edgeLaw beta J)
          (connEvent G (S : Set V) o {q.1} ∩ mpiSurfaceEvent G B S) := by
  rw [show (1 / beta) * mpiPhi G beta J o S *
      wprob (shk_edgeLaw beta J) (mpiSurfaceEvent G B S) =
        (1 / beta) * (mpiPhi G beta J o S *
          wprob (shk_edgeLaw beta J) (mpiSurfaceEvent G B S)) by ring,
    ← mpi_perSurface_eq_phi G beta J o B S, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q _
  have hprob : 0 ≤ wprob (shk_edgeLaw beta J)
      (connEvent G (S : Set V) o {q.1} ∩ mpiSurfaceEvent G B S) :=
    wprob_nonneg (fun e b => shk_edgeLaw_nonneg beta J hbeta.le hJ e b) _
  have hw := mpi_openWeight_div_beta_le beta (J s(q.1, q.2)) hbeta (hJ _)
  calc
    (1 / beta) *
        ((1 - Real.exp (-beta * J s(q.1, q.2))) *
          wprob (shk_edgeLaw beta J)
            (connEvent G (S : Set V) o {q.1} ∩ mpiSurfaceEvent G B S)) =
      ((1 / beta) * (1 - Real.exp (-beta * J s(q.1, q.2)))) *
        wprob (shk_edgeLaw beta J)
          (connEvent G (S : Set V) o {q.1} ∩ mpiSurfaceEvent G B S) := by ring
    _ ≤ J s(q.1, q.2) * wprob (shk_edgeLaw beta J)
          (connEvent G (S : Set V) o {q.1} ∩ mpiSurfaceEvent G B S) :=
      mul_le_mul_of_nonneg_right hw hprob




def mpiPivotalClosed (e : Sym2 V) (A : Set (ConfigSpace (Sym2 V))) :
    Set (ConfigSpace (Sym2 V)) :=
  {omega | IsPivotal e A omega ∧ omega e = false}

theorem mpi_setClosed_eq_of_false {e : Sym2 V} {omega : ConfigSpace (Sym2 V)}
    (he : omega e = false) : setClosed e omega = omega := by
  funext j
  by_cases hje : j = e
  · subst j
    simpa [he] using setClosed_self e omega
  · exact setClosed_of_ne hje omega


theorem mpi_pivotalClosed_subset_compl {e : Sym2 V}
    {A : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) :
    mpiPivotalClosed e A ⊆ Aᶜ := by
  intro omega h
  obtain ⟨hpiv, he⟩ := h
  have hnot := (isPivotal_iff_of_isIncreasing hA omega).mp hpiv |>.1
  rw [mpi_setClosed_eq_of_false he] at hnot
  exact hnot



theorem mpi_conn_surface_subset_pivotalClosed (o : V) (B : Set V)
    (S : Finset V) (ho : o ∈ S) {q : V × V}
    (hq : q ∈ shk_boundaryPairs G S) :
    connEvent G (S : Set V) o {q.1} ∩ mpiSurfaceEvent G B S ⊆
      mpiPivotalClosed s(q.1, q.2) (mpiCrossingEvent G o B) := by
  rintro omega ⟨hconn, hsurf⟩
  obtain ⟨hx, hy, hadj⟩ := (shk_mem_boundaryPairs G S).mp hq
  have hpiv := mpi_boundary_edge_isPivotal G o B omega hsurf ho hx hy hadj hconn
  have hclosed := mpi_boundary_edge_closed G B omega hsurf hx hy hadj
  exact ⟨hpiv, hclosed⟩



theorem mpi_wprob_eq_sum_inter_surfaces
    (phi : Sym2 V → Bool → ℝ) (o : V) (B : Set V)
    (C : Set (ConfigSpace (Sym2 V))) (hC : C ⊆ (mpiCrossingEvent G o B)ᶜ) :
    wprob phi C =
      ∑ S ∈ (Finset.univ.filter fun S : Finset V => o ∈ S),
        wprob phi (C ∩ mpiSurfaceEvent G B S) := by
  classical
  unfold wprob
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro omega _
  by_cases homega : omega ∈ C
  · rw [Set.indicator_of_mem homega, one_mul]
    have hncross : omega ∉ mpiCrossingEvent G o B := hC homega
    let S0 := mpiBlockedSet G B omega
    have hoS0 : o ∈ S0 := (mpi_not_crossing_iff_mem_blockedSet G o B omega).mp hncross
    have hS0mem : S0 ∈ (Finset.univ.filter fun S : Finset V => o ∈ S) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hoS0⟩
    symm
    calc
      (∑ S ∈ (Finset.univ.filter fun S : Finset V => o ∈ S),
          (C ∩ mpiSurfaceEvent G B S).indicator (fun _ => (1 : ℝ)) omega *
            pweight phi omega) =
          (C ∩ mpiSurfaceEvent G B S0).indicator (fun _ => (1 : ℝ)) omega *
            pweight phi omega := by
        apply Finset.sum_eq_single S0
        · intro S _ hSne
          rw [Set.indicator_of_notMem]
          · exact zero_mul _
          · rintro ⟨_, heq⟩
            exact hSne heq.symm
        · exact fun hnot => False.elim (hnot hS0mem)
      _ = pweight phi omega := by
        have hmem : omega ∈ C ∩ mpiSurfaceEvent G B S0 :=
          ⟨homega, show mpiBlockedSet G B omega = S0 from rfl⟩
        rw [Set.indicator_of_mem hmem, one_mul]
  · rw [Set.indicator_of_notMem homega, zero_mul]
    symm
    apply Finset.sum_eq_zero
    intro S _
    rw [Set.indicator_of_notMem]
    · exact zero_mul _
    · exact fun h => homega h.1



theorem mpi_boundaryJ_le_edgePivotal_surface (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 < beta) (hJ : ∀ e, 0 ≤ J e)
    (o : V) (B : Set V) (S : Finset V) (ho : o ∈ S) :
    (∑ q ∈ shk_boundaryPairs G S,
        J s(q.1, q.2) * wprob (shk_edgeLaw beta J)
          (connEvent G (S : Set V) o {q.1} ∩ mpiSurfaceEvent G B S)) ≤
      ∑ e ∈ G.edgeFinset,
        J e * wprob (shk_edgeLaw beta J)
          (mpiPivotalClosed e (mpiCrossingEvent G o B) ∩ mpiSurfaceEvent G B S) := by
  let f : Sym2 V → ℝ := fun e => J e * wprob (shk_edgeLaw beta J)
    (mpiPivotalClosed e (mpiCrossingEvent G o B) ∩ mpiSurfaceEvent G B S)
  have hinj : Set.InjOn (fun q : V × V => s(q.1, q.2))
      (shk_boundaryPairs G S : Set (V × V)) := by
    intro q hq r hr hqr
    obtain ⟨qx, qy, _⟩ := (shk_mem_boundaryPairs G S).mp hq
    obtain ⟨rx, ry, _⟩ := (shk_mem_boundaryPairs G S).mp hr
    rw [Sym2.eq_iff] at hqr
    rcases hqr with h | h
    · exact Prod.ext h.1 h.2
    · have : q.2 ∈ S := by rw [h.2]; exact rx
      exact False.elim (qy this)
  have himage : (shk_boundaryPairs G S).image (fun q => s(q.1, q.2)) ⊆
      G.edgeFinset := by
    intro e he
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp he
    rw [SimpleGraph.mem_edgeFinset]
    exact (shk_mem_boundaryPairs G S).mp hq |>.2.2
  calc
    (∑ q ∈ shk_boundaryPairs G S,
        J s(q.1, q.2) * wprob (shk_edgeLaw beta J)
          (connEvent G (S : Set V) o {q.1} ∩ mpiSurfaceEvent G B S)) ≤
      ∑ q ∈ shk_boundaryPairs G S, f s(q.1, q.2) := by
        apply Finset.sum_le_sum
        intro q hq
        apply mul_le_mul_of_nonneg_left _ (hJ _)
        apply wprob_mono (fun e b => shk_edgeLaw_nonneg beta J hbeta.le hJ e b)
        intro omega h
        exact ⟨mpi_conn_surface_subset_pivotalClosed G o B S ho hq h, h.2⟩
    _ = ∑ e ∈ (shk_boundaryPairs G S).image (fun q => s(q.1, q.2)), f e := by
        symm
        exact Finset.sum_image hinj
    _ ≤ ∑ e ∈ G.edgeFinset, f e := by
        apply Finset.sum_le_sum_of_subset_of_nonneg himage
        intro e _ _
        exact mul_nonneg (hJ e)
          (wprob_nonneg (fun j b => shk_edgeLaw_nonneg beta J hbeta.le hJ j b) _)



theorem mpi_surface_reassembly (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 < beta) (hJ : ∀ e, 0 ≤ J e)
    (o : V) (B : Set V) (m : ℝ)
    (hm : ∀ S : Finset V, o ∈ S → m ≤ mpiPhi G beta J o S) :
    (1 / beta) * m *
        (1 - wprob (shk_edgeLaw beta J) (mpiCrossingEvent G o B)) ≤
      ∑ e ∈ G.edgeFinset, J e * wprob (shk_edgeLaw beta J)
        (mpiPivotalClosed e (mpiCrossingEvent G o B)) := by
  let P : Finset (Finset V) := Finset.univ.filter fun S => o ∈ S
  have hmass : 1 - wprob (shk_edgeLaw beta J) (mpiCrossingEvent G o B) =
      ∑ S ∈ P, wprob (shk_edgeLaw beta J) (mpiSurfaceEvent G B S) := by
    rw [← mpi_wprob_compl (shk_edgeLaw beta J) (shk_edgeLaw_sum_one beta J)]
    exact mpi_wprob_crossing_compl_eq_sum_surfaces G
      (shk_edgeLaw beta J) (shk_edgeLaw_sum_one beta J) o B
  calc
    (1 / beta) * m *
        (1 - wprob (shk_edgeLaw beta J) (mpiCrossingEvent G o B)) =
      ∑ S ∈ P, (1 / beta) * m *
        wprob (shk_edgeLaw beta J) (mpiSurfaceEvent G B S) := by
          rw [hmass, Finset.mul_sum]
    _ ≤ ∑ S ∈ P, ∑ e ∈ G.edgeFinset,
        J e * wprob (shk_edgeLaw beta J)
          (mpiPivotalClosed e (mpiCrossingEvent G o B) ∩ mpiSurfaceEvent G B S) := by
      apply Finset.sum_le_sum
      intro S hS
      have hoS : o ∈ S := (Finset.mem_filter.mp hS).2
      have hsurf : 0 ≤ wprob (shk_edgeLaw beta J) (mpiSurfaceEvent G B S) :=
        wprob_nonneg (fun e b => shk_edgeLaw_nonneg beta J hbeta.le hJ e b) _
      calc
        (1 / beta) * m * wprob (shk_edgeLaw beta J) (mpiSurfaceEvent G B S) ≤
          (1 / beta) * mpiPhi G beta J o S *
            wprob (shk_edgeLaw beta J) (mpiSurfaceEvent G B S) := by
              apply mul_le_mul_of_nonneg_right _ hsurf
              exact mul_le_mul_of_nonneg_left (hm S hoS) (by positivity)
        _ ≤ ∑ q ∈ shk_boundaryPairs G S,
            J s(q.1, q.2) * wprob (shk_edgeLaw beta J)
              (connEvent G (S : Set V) o {q.1} ∩ mpiSurfaceEvent G B S) :=
          mpi_phi_surface_le_boundaryJ G beta J hbeta hJ o B S
        _ ≤ ∑ e ∈ G.edgeFinset,
            J e * wprob (shk_edgeLaw beta J)
              (mpiPivotalClosed e (mpiCrossingEvent G o B) ∩ mpiSurfaceEvent G B S) :=
          mpi_boundaryJ_le_edgePivotal_surface G beta J hbeta hJ o B S hoS
    _ = ∑ e ∈ G.edgeFinset, J e * wprob (shk_edgeLaw beta J)
        (mpiPivotalClosed e (mpiCrossingEvent G o B)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      rw [← Finset.mul_sum]
      congr 1
      symm
      exact mpi_wprob_eq_sum_inter_surfaces G (shk_edgeLaw beta J) o B
        (mpiPivotalClosed e (mpiCrossingEvent G o B))
        (mpi_pivotalClosed_subset_compl (isIncreasing_connEvent G Set.univ o B))





theorem mpi_surface_reassembly_of_nonempty (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 < beta) (hJ : ∀ e, 0 ≤ J e)
    (o : V) (B : Set V) (m : ℝ)
    (hm : ∀ S : Finset V, o ∈ S →
      (mpiSurfaceEvent G B S).Nonempty → m ≤ mpiPhi G beta J o S) :
    (1 / beta) * m *
        (1 - wprob (shk_edgeLaw beta J) (mpiCrossingEvent G o B)) ≤
      ∑ e ∈ G.edgeFinset, J e * wprob (shk_edgeLaw beta J)
        (mpiPivotalClosed e (mpiCrossingEvent G o B)) := by
  let P : Finset (Finset V) := Finset.univ.filter fun S => o ∈ S
  have hmass : 1 - wprob (shk_edgeLaw beta J) (mpiCrossingEvent G o B) =
      ∑ S ∈ P, wprob (shk_edgeLaw beta J) (mpiSurfaceEvent G B S) := by
    rw [← mpi_wprob_compl (shk_edgeLaw beta J) (shk_edgeLaw_sum_one beta J)]
    exact mpi_wprob_crossing_compl_eq_sum_surfaces G
      (shk_edgeLaw beta J) (shk_edgeLaw_sum_one beta J) o B
  calc
    (1 / beta) * m *
        (1 - wprob (shk_edgeLaw beta J) (mpiCrossingEvent G o B)) =
      ∑ S ∈ P, (1 / beta) * m *
        wprob (shk_edgeLaw beta J) (mpiSurfaceEvent G B S) := by
          rw [hmass, Finset.mul_sum]
    _ ≤ ∑ S ∈ P, ∑ e ∈ G.edgeFinset,
        J e * wprob (shk_edgeLaw beta J)
          (mpiPivotalClosed e (mpiCrossingEvent G o B) ∩ mpiSurfaceEvent G B S) := by
      apply Finset.sum_le_sum
      intro S hS
      have hoS : o ∈ S := (Finset.mem_filter.mp hS).2
      by_cases hocc : (mpiSurfaceEvent G B S).Nonempty
      · have hsurf : 0 ≤ wprob (shk_edgeLaw beta J) (mpiSurfaceEvent G B S) :=
          wprob_nonneg (fun e b => shk_edgeLaw_nonneg beta J hbeta.le hJ e b) _
        calc
          (1 / beta) * m * wprob (shk_edgeLaw beta J) (mpiSurfaceEvent G B S) ≤
              (1 / beta) * mpiPhi G beta J o S *
                wprob (shk_edgeLaw beta J) (mpiSurfaceEvent G B S) := by
            apply mul_le_mul_of_nonneg_right _ hsurf
            exact mul_le_mul_of_nonneg_left (hm S hoS hocc) (by positivity)
          _ ≤ ∑ q ∈ shk_boundaryPairs G S,
              J s(q.1, q.2) * wprob (shk_edgeLaw beta J)
                (connEvent G (S : Set V) o {q.1} ∩ mpiSurfaceEvent G B S) :=
            mpi_phi_surface_le_boundaryJ G beta J hbeta hJ o B S
          _ ≤ ∑ e ∈ G.edgeFinset,
              J e * wprob (shk_edgeLaw beta J)
                (mpiPivotalClosed e (mpiCrossingEvent G o B) ∩
                  mpiSurfaceEvent G B S) :=
            mpi_boundaryJ_le_edgePivotal_surface G beta J hbeta hJ o B S hoS
      · have hempty : mpiSurfaceEvent G B S = ∅ :=
          Set.not_nonempty_iff_eq_empty.mp hocc
        rw [hempty]
        simp [wprob]
    _ = ∑ e ∈ G.edgeFinset, J e * wprob (shk_edgeLaw beta J)
        (mpiPivotalClosed e (mpiCrossingEvent G o B)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      rw [← Finset.mul_sum]
      congr 1
      symm
      exact mpi_wprob_eq_sum_inter_surfaces G (shk_edgeLaw beta J) o B
        (mpiPivotalClosed e (mpiCrossingEvent G o B))
        (mpi_pivotalClosed_subset_compl (isIncreasing_connEvent G Set.univ o B))




noncomputable def mpiWeightOff (beta : ℝ) (J : Sym2 V → ℝ)
    (e : Sym2 V) (omega : ConfigSpace (Sym2 V)) : ℝ :=
  ∏ j ∈ Finset.univ.erase e, shk_edgeLaw beta J j (omega j)

theorem mpi_pweight_eq_edge_mul_off (beta : ℝ) (J : Sym2 V → ℝ)
    (e : Sym2 V) (omega : ConfigSpace (Sym2 V)) :
    pweight (shk_edgeLaw beta J) omega =
      shk_edgeLaw beta J e (omega e) * mpiWeightOff beta J e omega := by
  unfold pweight mpiWeightOff
  exact (Finset.mul_prod_erase Finset.univ
    (fun j => shk_edgeLaw beta J j (omega j)) (Finset.mem_univ e)).symm

theorem mpi_weightOff_congr (beta : ℝ) (J : Sym2 V → ℝ) (e : Sym2 V)
    {omega omega' : ConfigSpace (Sym2 V)}
    (h : ∀ j, j ≠ e → omega j = omega' j) :
    mpiWeightOff beta J e omega = mpiWeightOff beta J e omega' := by
  unfold mpiWeightOff
  apply Finset.prod_congr rfl
  intro j hj
  rw [Finset.mem_erase] at hj
  rw [h j hj.1]


theorem mpi_hasDerivAt_pweight (J : Sym2 V → ℝ) (beta : ℝ)
    (omega : ConfigSpace (Sym2 V)) :
    HasDerivAt (fun b => pweight (shk_edgeLaw b J) omega)
      (∑ e, mpiWeightOff beta J e omega *
        (if omega e then J e * Real.exp (-(beta * J e))
          else -(J e * Real.exp (-(beta * J e))))) beta := by
  unfold pweight mpiWeightOff shk_edgeLaw
  have h := HasDerivAt.fun_finsetProd (u := (Finset.univ : Finset (Sym2 V)))
    (f := fun e b => if omega e then 1 - Real.exp (-b * J e) else Real.exp (-b * J e))
    (f' := fun e => if omega e then J e * Real.exp (-(beta * J e))
      else -(J e * Real.exp (-(beta * J e))))
    (x := beta) (fun e _ => by
      simpa [FK.betaParams] using FK.hasDerivAt_betaFactor J omega e beta)
  simpa [smul_eq_mul] using h



theorem mpi_perEdge_beta_pivotal (beta : ℝ) (J : Sym2 V → ℝ)
    (A : Set (ConfigSpace (Sym2 V))) (hA : IsIncreasing A) (e : Sym2 V) :
    (∑ omega, A.indicator (fun _ => (1 : ℝ)) omega *
      (mpiWeightOff beta J e omega *
        (if omega e then J e * Real.exp (-(beta * J e))
          else -(J e * Real.exp (-(beta * J e)))))) =
      J e * wprob (shk_edgeLaw beta J) (mpiPivotalClosed e A) := by
  unfold wprob
  rw [← Equiv.sum_comp (Equiv.funSplitAt e Bool).symm
      (fun omega => A.indicator (fun _ => (1 : ℝ)) omega *
        (mpiWeightOff beta J e omega *
          (if omega e then J e * Real.exp (-(beta * J e))
            else -(J e * Real.exp (-(beta * J e))))))]
  rw [← Equiv.sum_comp (Equiv.funSplitAt e Bool).symm
      (fun omega => (mpiPivotalClosed e A).indicator (fun _ => (1 : ℝ)) omega *
        pweight (shk_edgeLaw beta J) omega)]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type,
    Fintype.sum_bool, Fintype.sum_bool,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro eta _
  let omegaT := (Equiv.funSplitAt e Bool).symm (true, eta)
  let omegaF := (Equiv.funSplitAt e Bool).symm (false, eta)
  change A.indicator (fun _ => (1 : ℝ)) omegaT *
      (mpiWeightOff beta J e omegaT *
        (if omegaT e then J e * Real.exp (-(beta * J e))
          else -(J e * Real.exp (-(beta * J e))))) +
      A.indicator (fun _ => (1 : ℝ)) omegaF *
      (mpiWeightOff beta J e omegaF *
        (if omegaF e then J e * Real.exp (-(beta * J e))
          else -(J e * Real.exp (-(beta * J e))))) =
    J e * ((mpiPivotalClosed e A).indicator (fun _ => (1 : ℝ)) omegaT *
      pweight (shk_edgeLaw beta J) omegaT +
      (mpiPivotalClosed e A).indicator (fun _ => (1 : ℝ)) omegaF *
      pweight (shk_edgeLaw beta J) omegaF)
  have ht : omegaT e = true := by
    simp [omegaT, Equiv.funSplitAt, Equiv.piSplitAt]
  have hf : omegaF e = false := by
    simp [omegaF, Equiv.funSplitAt, Equiv.piSplitAt]
  have hsame : ∀ j, j ≠ e → omegaT j = omegaF j := by
    intro j hj
    simp [omegaT, omegaF, Equiv.funSplitAt, Equiv.piSplitAt, hj]
  have hto : setOpen e omegaT = omegaT := by
    funext j
    by_cases hje : j = e
    · subst j
      rw [setOpen_self, ht]
    · rw [setOpen_of_ne hje]
  have htc : setClosed e omegaT = omegaF := by
    funext j
    by_cases hje : j = e
    · subst j
      rw [setClosed_self, hf]
    · rw [setClosed_of_ne hje, hsame j hje]
  have hoff : mpiWeightOff beta J e omegaT = mpiWeightOff beta J e omegaF :=
    mpi_weightOff_congr beta J e hsame
  have hpiv : IsPivotal e A omegaT ↔ (omegaF ∉ A ∧ omegaT ∈ A) := by
    rw [isPivotal_iff_of_isIncreasing hA, hto, htc]
  have hpivEq : IsPivotal e A omegaT ↔ IsPivotal e A omegaF := by
    apply isPivotal_congr
    intro j hj
    exact hsame j hj
  have hwF : pweight (shk_edgeLaw beta J) omegaF =
      Real.exp (-(beta * J e)) * mpiWeightOff beta J e omegaF := by
    rw [mpi_pweight_eq_edge_mul_off beta J e omegaF]
    simp [shk_edgeLaw, hf]
  have hTnot : omegaT ∉ mpiPivotalClosed e A := by
    intro h
    exact Bool.noConfusion (ht.symm.trans h.2)
  by_cases hmt : omegaT ∈ A <;> by_cases hmf : omegaF ∈ A
  · have hnp : ¬ IsPivotal e A omegaT := by rw [hpiv]; tauto
    have hFnot : omegaF ∉ mpiPivotalClosed e A := by
      intro h
      exact (hpivEq.not.mp hnp) h.1
    simp [Set.indicator_of_mem hmt, Set.indicator_of_mem hmf,
      Set.indicator_of_notMem hTnot, Set.indicator_of_notMem hFnot, ht, hf, hoff]
  · have hp : IsPivotal e A omegaT := hpiv.mpr ⟨hmf, hmt⟩
    have hFmem : omegaF ∈ mpiPivotalClosed e A := ⟨hpivEq.mp hp, hf⟩
    rw [Set.indicator_of_mem hmt, Set.indicator_of_notMem hmf,
      Set.indicator_of_notMem hTnot, Set.indicator_of_mem hFmem]
    simp only [ht, hf, if_true, if_false, one_mul, zero_mul, zero_add, hwF]
    rw [hoff]
    ring
  · exfalso
    have hle : omegaF ≤ omegaT := by
      intro j
      by_cases hje : j = e
      · subst j
        rw [hf, ht]
        exact bot_le
      · rw [hsame j hje]
    exact hmt (hA hle hmf)
  · have hnp : ¬ IsPivotal e A omegaT := by rw [hpiv]; tauto
    have hFnot : omegaF ∉ mpiPivotalClosed e A := by
      intro h
      exact (hpivEq.not.mp hnp) h.1
    simp [Set.indicator_of_notMem hmt, Set.indicator_of_notMem hmf,
      Set.indicator_of_notMem hTnot, Set.indicator_of_notMem hFnot, ht, hf]



theorem mpi_hasDerivAt_wprob (beta : ℝ) (J : Sym2 V → ℝ)
    (A : Set (ConfigSpace (Sym2 V))) (hA : IsIncreasing A) :
    HasDerivAt (fun b => wprob (shk_edgeLaw b J) A)
      (∑ e, J e * wprob (shk_edgeLaw beta J) (mpiPivotalClosed e A)) beta := by
  change HasDerivAt
    (fun b => ∑ omega, A.indicator (fun _ => (1 : ℝ)) omega *
      pweight (shk_edgeLaw b J) omega) _ beta
  have hd := HasDerivAt.fun_sum (u := (Finset.univ : Finset (ConfigSpace (Sym2 V))))
    (fun omega _ => (mpi_hasDerivAt_pweight J beta omega).const_mul
      (A.indicator (fun _ => (1 : ℝ)) omega))
  refine hd.congr_deriv ?_
  rw [show (∑ omega, A.indicator (fun _ => (1 : ℝ)) omega *
        (∑ e, mpiWeightOff beta J e omega *
          (if omega e then J e * Real.exp (-(beta * J e))
            else -(J e * Real.exp (-(beta * J e)))))) =
      ∑ omega, ∑ e, A.indicator (fun _ => (1 : ℝ)) omega *
        (mpiWeightOff beta J e omega *
          (if omega e then J e * Real.exp (-(beta * J e))
            else -(J e * Real.exp (-(beta * J e))))) by
      apply Finset.sum_congr rfl
      intro omega _
      rw [Finset.mul_sum], Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  exact mpi_perEdge_beta_pivotal beta J A hA e













theorem mpi_meanfield_perco (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 < beta) (hJ : ∀ e, 0 ≤ J e)
    (o : V) (B : Set V) (m : ℝ)
    (hm : ∀ S : Finset V, o ∈ S → m ≤ mpiPhi G beta J o S) :
    HasDerivAt
        (fun b => wprob (shk_edgeLaw b J) (mpiCrossingEvent G o B))
        (∑ e, J e * wprob (shk_edgeLaw beta J)
          (mpiPivotalClosed e (mpiCrossingEvent G o B))) beta ∧
      (1 / beta) * m *
          (1 - wprob (shk_edgeLaw beta J) (mpiCrossingEvent G o B)) ≤
        ∑ e, J e * wprob (shk_edgeLaw beta J)
          (mpiPivotalClosed e (mpiCrossingEvent G o B)) := by
  refine ⟨mpi_hasDerivAt_wprob beta J (mpiCrossingEvent G o B)
    (isIncreasing_connEvent G Set.univ o B), ?_⟩
  have hs := mpi_surface_reassembly G beta J hbeta hJ o B m hm
  apply hs.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact fun e he => Finset.mem_univ e
  · intro e _ _
    exact mul_nonneg (hJ e)
      (wprob_nonneg (fun j b => shk_edgeLaw_nonneg beta J hbeta.le hJ j b) _)



theorem mpi_meanfield_perco_of_nonempty (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 < beta) (hJ : ∀ e, 0 ≤ J e)
    (o : V) (B : Set V) (m : ℝ)
    (hm : ∀ S : Finset V, o ∈ S →
      (mpiSurfaceEvent G B S).Nonempty → m ≤ mpiPhi G beta J o S) :
    HasDerivAt
        (fun b => wprob (shk_edgeLaw b J) (mpiCrossingEvent G o B))
        (∑ e, J e * wprob (shk_edgeLaw beta J)
          (mpiPivotalClosed e (mpiCrossingEvent G o B))) beta ∧
      (1 / beta) * m *
          (1 - wprob (shk_edgeLaw beta J) (mpiCrossingEvent G o B)) ≤
        ∑ e, J e * wprob (shk_edgeLaw beta J)
          (mpiPivotalClosed e (mpiCrossingEvent G o B)) := by
  refine ⟨mpi_hasDerivAt_wprob beta J (mpiCrossingEvent G o B)
    (isIncreasing_connEvent G Set.univ o B), ?_⟩
  have hs := mpi_surface_reassembly_of_nonempty G beta J hbeta hJ o B m hm
  apply hs.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact fun e he => Finset.mem_univ e
  · intro e _ _
    exact mul_nonneg (hJ e)
      (wprob_nonneg (fun j b => shk_edgeLaw_nonneg beta J hbeta.le hJ j b) _)




theorem mpi_meanfield_perco_of_disjoint (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 < beta) (hJ : ∀ e, 0 ≤ J e)
    (o : V) (B : Set V) (m : ℝ)
    (hm : ∀ S : Finset V, o ∈ S → Disjoint (S : Set V) B →
      m ≤ mpiPhi G beta J o S) :
    HasDerivAt
        (fun b => wprob (shk_edgeLaw b J) (mpiCrossingEvent G o B))
        (∑ e, J e * wprob (shk_edgeLaw beta J)
          (mpiPivotalClosed e (mpiCrossingEvent G o B))) beta ∧
      (1 / beta) * m *
          (1 - wprob (shk_edgeLaw beta J) (mpiCrossingEvent G o B)) ≤
        ∑ e, J e * wprob (shk_edgeLaw beta J)
          (mpiPivotalClosed e (mpiCrossingEvent G o B)) := by
  apply mpi_meanfield_perco_of_nonempty G beta J hbeta hJ o B m
  intro S hoS hocc
  exact hm S hoS (mpi_surfaceEvent_nonempty_disjoint G B S hocc)

end Sharpness
end StatMech
