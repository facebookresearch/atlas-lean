/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicDirichletComparison
import Code.FrontierB.BoxGraphPath












open Finset SimpleGraph Filter Set Topology

namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section


def fkIsingSquareBoxBoundary (n : Nat) (x : (fkSquareBoxPlanar n).V) : Prop :=
  ∃ i : Fin 2, (x.1 i).natAbs = n

theorem fkIsingSquareMarkedA_mem_boxBoundary (n : Nat) :
    fkIsingSquareBoxBoundary n (fkIsingSquareMarkedA n) := by
  refine ⟨0, ?_⟩
  simp [fkIsingSquareBoxBoundary, fkIsingSquareMarkedA]


theorem fkIsingSquareBox_reachable_boundary (n : Nat) :
    ∀ x : (fkSquareBoxPlanar n).V, ∃ b,
      fkIsingSquareBoxBoundary n b ∧
        (fkSquareBoxPlanar n).G.Reachable x b := by
  intro x
  refine ⟨fkIsingSquareMarkedA n,
    fkIsingSquareMarkedA_mem_boxBoundary n, ?_⟩
  exact StatMech.FrontierB.boxGraph_preconnected 2 n x
    (fkIsingSquareMarkedA n)


def fkIsingSquareBoxQuadraticBarrier
    (n : Nat) (x : (fkSquareBoxPlanar n).V) : Real :=
  (2 * (n : Real) ^ 2 - (x.1 0 : Real) ^ 2 -
    (x.1 1 : Real) ^ 2) / 4

private theorem fkIsingSquare_intCast_sq_le_nat_sq
    (z : Int) (n : Nat) (h : z.natAbs ≤ n) :
    (z : Real) ^ 2 ≤ (n : Real) ^ 2 := by
  have hc : (z.natAbs : Real) ≤ (n : Real) := by
    exact_mod_cast h
  have habs : |(z : Real)| ≤ (n : Real) := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hc
  simpa only [sq_abs] using
    (sq_le_sq₀ (abs_nonneg (z : Real)) (Nat.cast_nonneg n)).2 habs



theorem fkIsingSquareBoxQuadraticBarrier_laplacian
    (n : Nat) (x : (fkSquareBoxPlanar n).V)
    (hx : ¬ fkIsingSquareBoxBoundary n x) :
    isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G
      (fkIsingSquareBoxQuadraticBarrier n) x = -1 := by
  classical
  have hinterior (k : Fin 2) : (x.1 k).natAbs < n := by
    have hle := x.2 k
    have hne : (x.1 k).natAbs ≠ n := by
      intro heq
      exact hx ⟨k, heq⟩
    omega
  have heSite : shift 2 x.1 0 1 ∈ box 2 n := by
    intro k
    fin_cases k
    · change (x.1 0 + 1).natAbs ≤ n
      have htri := Int.natAbs_add_le (x.1 0) 1
      norm_num at htri
      have hi := hinterior 0
      omega
    · simpa [shift] using x.2 1
  have hwSite : shift 2 x.1 0 (-1) ∈ box 2 n := by
    intro k
    fin_cases k
    · change (x.1 0 + (-1)).natAbs ≤ n
      have htri := Int.natAbs_add_le (x.1 0) (-1)
      norm_num at htri
      have hi := hinterior 0
      omega
    · simpa [shift] using x.2 1
  have huSite : shift 2 x.1 1 1 ∈ box 2 n := by
    intro k
    fin_cases k
    · simpa [shift] using x.2 0
    · change (x.1 1 + 1).natAbs ≤ n
      have htri := Int.natAbs_add_le (x.1 1) 1
      norm_num at htri
      have hi := hinterior 1
      omega
  have hdSite : shift 2 x.1 1 (-1) ∈ box 2 n := by
    intro k
    fin_cases k
    · simpa [shift] using x.2 0
    · change (x.1 1 + (-1)).natAbs ≤ n
      have htri := Int.natAbs_add_le (x.1 1) (-1)
      norm_num at htri
      have hi := hinterior 1
      omega
  let e : (fkSquareBoxPlanar n).V := ⟨shift 2 x.1 0 1, heSite⟩
  let w : (fkSquareBoxPlanar n).V := ⟨shift 2 x.1 0 (-1), hwSite⟩
  let u : (fkSquareBoxPlanar n).V := ⟨shift 2 x.1 1 1, huSite⟩
  let d : (fkSquareBoxPlanar n).V := ⟨shift 2 x.1 1 (-1), hdSite⟩
  have hneighbors : (fkSquareBoxPlanar n).G.neighborFinset x =
      {e, w, u, d} := by
    ext y
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert,
      Finset.mem_singleton]
    change NearestNeighbour 2 x.1 y.1 ↔
      y = e ∨ y = w ∨ y = u ∨ y = d
    rw [nearestNeighbour_iff_shift]
    constructor
    · rintro ⟨k, s, hs, hys⟩
      fin_cases k <;> rcases hs with rfl | rfl
      · left
        apply Subtype.ext
        simpa [e] using hys
      · right; left
        apply Subtype.ext
        simpa [w] using hys
      · right; right; left
        apply Subtype.ext
        simpa [u] using hys
      · right; right; right
        apply Subtype.ext
        simpa [d] using hys
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨0, 1, Or.inl rfl, rfl⟩
      · exact ⟨0, -1, Or.inr rfl, rfl⟩
      · exact ⟨1, 1, Or.inl rfl, rfl⟩
      · exact ⟨1, -1, Or.inr rfl, rfl⟩
  have hew : e ≠ w := by
    intro h
    have hk := congrArg (fun z : (fkSquareBoxPlanar n).V ↦ z.1 0) h
    simp [e, w, shift] at hk
  have heu : e ≠ u := by
    intro h
    have hk := congrArg (fun z : (fkSquareBoxPlanar n).V ↦ z.1 0) h
    simp [e, u, shift] at hk
  have hed : e ≠ d := by
    intro h
    have hk := congrArg (fun z : (fkSquareBoxPlanar n).V ↦ z.1 0) h
    simp [e, d, shift] at hk
  have hwu : w ≠ u := by
    intro h
    have hk := congrArg (fun z : (fkSquareBoxPlanar n).V ↦ z.1 0) h
    simp [w, u, shift] at hk
  have hwd : w ≠ d := by
    intro h
    have hk := congrArg (fun z : (fkSquareBoxPlanar n).V ↦ z.1 0) h
    simp [w, d, shift] at hk
  have hud : u ≠ d := by
    intro h
    have hk := congrArg (fun z : (fkSquareBoxPlanar n).V ↦ z.1 1) h
    simp [u, d, shift] at hk
  have he_not : e ∉ ({w, u, d} : Finset (fkSquareBoxPlanar n).V) := by
    simp [hew, heu, hed]
  have hw_not : w ∉ ({u, d} : Finset (fkSquareBoxPlanar n).V) := by
    simp [hwu, hwd]
  have hu_not : u ∉ ({d} : Finset (fkSquareBoxPlanar n).V) := by
    simp [hud]
  unfold isingFiniteGraphLaplacian
  rw [hneighbors]
  rw [Finset.sum_insert he_not, Finset.sum_insert hw_not,
    Finset.sum_insert hu_not, Finset.sum_singleton]
  simp [fkIsingSquareBoxQuadraticBarrier, e, w, u, d, shift]
  ring

theorem fkIsingSquareBoxQuadraticBarrier_nonneg
    (n : Nat) (x : (fkSquareBoxPlanar n).V) :
    0 ≤ fkIsingSquareBoxQuadraticBarrier n x := by
  have h0 := fkIsingSquare_intCast_sq_le_nat_sq (x.1 0) n (x.2 0)
  have h1 := fkIsingSquare_intCast_sq_le_nat_sq (x.1 1) n (x.2 1)
  unfold fkIsingSquareBoxQuadraticBarrier
  nlinarith

theorem fkIsingSquareBoxQuadraticBarrier_le
    (n : Nat) (x : (fkSquareBoxPlanar n).V) :
    fkIsingSquareBoxQuadraticBarrier n x ≤ (n : Real) ^ 2 / 2 := by
  have h0 : 0 ≤ (x.1 0 : Real) ^ 2 := sq_nonneg _
  have h1 : 0 ≤ (x.1 1 : Real) ^ 2 := sq_nonneg _
  unfold fkIsingSquareBoxQuadraticBarrier
  nlinarith

noncomputable def fkIsingSquareBoxCanonicalPoissonBarrier
    (n : Nat) : (fkSquareBoxPlanar n).V → Real := by
  letI : Nonempty (fkSquareBoxPlanar n).V :=
    ⟨fkIsingSquareMarkedA n⟩
  exact isingFiniteGraphPoissonBarrier
    (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n)
    (fkIsingSquareBox_reachable_boundary n)

noncomputable def fkIsingSquareBoxCanonicalPoissonBarrierBound
    (n : Nat) : Real := by
  letI : Nonempty (fkSquareBoxPlanar n).V :=
    ⟨fkIsingSquareMarkedA n⟩
  exact isingFiniteGraphPoissonBarrierBound
    (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n)
    (fkIsingSquareBox_reachable_boundary n)



theorem fkIsingSquareBoxPoissonBarrier_le_quadratic
    (n : Nat) : ∀ x,
    fkIsingSquareBoxCanonicalPoissonBarrier n x ≤
      fkIsingSquareBoxQuadraticBarrier n x := by
  letI : Nonempty (fkSquareBoxPlanar n).V :=
    ⟨fkIsingSquareMarkedA n⟩
  change ∀ x, isingFiniteGraphPoissonBarrier
      (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n)
      (fkIsingSquareBox_reachable_boundary n) x ≤
    fkIsingSquareBoxQuadraticBarrier n x
  apply isingFiniteGraph_laplacian_comparison
    (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n)
    (isingFiniteGraphPoissonBarrier
      (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n)
      (fkIsingSquareBox_reachable_boundary n))
    (fkIsingSquareBoxQuadraticBarrier n)
    (fkIsingSquareBox_reachable_boundary n)
  · intro x hx
    rw [isingFiniteGraphPoissonBarrier_boundary
      (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n)
      (fkIsingSquareBox_reachable_boundary n) x hx]
    exact fkIsingSquareBoxQuadraticBarrier_nonneg n x
  · intro x hx
    rw [fkIsingSquareBoxQuadraticBarrier_laplacian n x hx,
      isingFiniteGraphPoissonBarrier_laplacian
        (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n)
        (fkIsingSquareBox_reachable_boundary n) x hx]



theorem fkIsingSquareBoxPoissonBarrierBound_le (n : Nat) :
    fkIsingSquareBoxCanonicalPoissonBarrierBound n ≤
      (n : Real) ^ 2 / 2 := by
  letI : Nonempty (fkSquareBoxPlanar n).V :=
    ⟨fkIsingSquareMarkedA n⟩
  change isingFiniteGraphPoissonBarrierBound
      (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n)
      (fkIsingSquareBox_reachable_boundary n) ≤ (n : Real) ^ 2 / 2
  unfold isingFiniteGraphPoissonBarrierBound
  rw [Finset.max'_le_iff]
  intro z hz
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hz
  exact (fkIsingSquareBoxPoissonBarrier_le_quadratic n x).trans
    (fkIsingSquareBoxQuadraticBarrier_le n x)



theorem fkIsingSquare_harmonic_boundary_stability
    (n : Nat) (u v : (fkSquareBoxPlanar n).V → Real) (eps : Real)
    (hu : IsingFiniteGraphHarmonicOn (fkSquareBoxPlanar n).G
      (fkIsingSquareBoxBoundary n) u)
    (hv : IsingFiniteGraphHarmonicOn (fkSquareBoxPlanar n).G
      (fkIsingSquareBoxBoundary n) v)
    (hboundary : ∀ x, fkIsingSquareBoxBoundary n x →
      |u x - v x| ≤ eps) :
    ∀ x, |u x - v x| ≤ eps := by
  letI : Nonempty (fkSquareBoxPlanar n).V :=
    ⟨fkIsingSquareMarkedA n⟩
  exact isingFiniteGraph_harmonic_boundary_stability
    (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n)
      u v eps (fkIsingSquareBox_reachable_boundary n) hu hv hboundary




theorem fkIsingSquare_dirichlet_sandwich_stability
    (n : Nat) (upper lower harmonic f : (fkSquareBoxPlanar n).V → Real)
    (eps : Real)
    (hupper : IsingFiniteGraphSubharmonicOn (fkSquareBoxPlanar n).G
      (fkIsingSquareBoxBoundary n) upper)
    (hlower : IsingFiniteGraphSuperharmonicOn (fkSquareBoxPlanar n).G
      (fkIsingSquareBoxBoundary n) lower)
    (hharmonic : IsingFiniteGraphHarmonicOn (fkSquareBoxPlanar n).G
      (fkIsingSquareBoxBoundary n) harmonic)
    (hupperBoundary : ∀ x, fkIsingSquareBoxBoundary n x →
      upper x ≤ harmonic x + eps)
    (hlowerBoundary : ∀ x, fkIsingSquareBoxBoundary n x →
      harmonic x ≤ lower x + eps)
    (hsandwich : ∀ x, lower x ≤ f x ∧ f x ≤ upper x) :
    ∀ x, |f x - harmonic x| ≤ eps := by
  letI : Nonempty (fkSquareBoxPlanar n).V :=
    ⟨fkIsingSquareMarkedA n⟩
  have hup : ∀ x, upper x ≤ harmonic x + eps := by
    apply isingFiniteGraph_subharmonic_le_harmonic
      (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n)
      upper (fun x ↦ harmonic x + eps)
      (fkIsingSquareBox_reachable_boundary n) hupper
      (hharmonic.add_const eps) hupperBoundary
  have hlo : ∀ x, harmonic x ≤ lower x + eps := by
    apply isingFiniteGraph_harmonic_le_superharmonic
      (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n)
      harmonic (fun x ↦ lower x + eps)
      (fkIsingSquareBox_reachable_boundary n) hharmonic
    · intro x hx
      rw [isingFiniteGraphLaplacian_add_const]
      exact hlower x hx
    · exact hlowerBoundary
  intro x
  rw [abs_le]
  rcases hsandwich x with ⟨hxf, hfx⟩
  constructor <;> linarith [hup x, hlo x]



theorem fkIsingSquare_harmonic_uniform_convergence_of_boundary
    (u v : ∀ n, (fkSquareBoxPlanar n).V → Real)
    (eps : Nat → Real)
    (hu : ∀ n, IsingFiniteGraphHarmonicOn (fkSquareBoxPlanar n).G
      (fkIsingSquareBoxBoundary n) (u n))
    (hv : ∀ n, IsingFiniteGraphHarmonicOn (fkSquareBoxPlanar n).G
      (fkIsingSquareBoxBoundary n) (v n))
    (hboundary : ∀ n x, fkIsingSquareBoxBoundary n x →
      |u n x - v n x| ≤ eps n)
    (heps : Tendsto eps atTop (nhds 0)) :
    ∀ eta : Real, 0 < eta →
      ∀ᶠ n in atTop, ∀ x, |u n x - v n x| < eta := by
  intro eta heta
  have hevent : ∀ᶠ n in atTop, eps n < eta :=
    heps (Iio_mem_nhds heta)
  filter_upwards [hevent] with n hn
  intro x
  exact lt_of_le_of_lt
    (fkIsingSquare_harmonic_boundary_stability n (u n) (v n)
      (eps n) (hu n) (hv n) (hboundary n) x) hn



theorem fkIsingSquare_dirichlet_sandwich_uniform_convergence
    (upper lower harmonic f : ∀ n, (fkSquareBoxPlanar n).V → Real)
    (eps : Nat → Real)
    (hupper : ∀ n, IsingFiniteGraphSubharmonicOn (fkSquareBoxPlanar n).G
      (fkIsingSquareBoxBoundary n) (upper n))
    (hlower : ∀ n, IsingFiniteGraphSuperharmonicOn (fkSquareBoxPlanar n).G
      (fkIsingSquareBoxBoundary n) (lower n))
    (hharmonic : ∀ n, IsingFiniteGraphHarmonicOn (fkSquareBoxPlanar n).G
      (fkIsingSquareBoxBoundary n) (harmonic n))
    (hupperBoundary : ∀ n x, fkIsingSquareBoxBoundary n x →
      upper n x ≤ harmonic n x + eps n)
    (hlowerBoundary : ∀ n x, fkIsingSquareBoxBoundary n x →
      harmonic n x ≤ lower n x + eps n)
    (hsandwich : ∀ n x, lower n x ≤ f n x ∧ f n x ≤ upper n x)
    (heps : Tendsto eps atTop (nhds 0)) :
    ∀ eta : Real, 0 < eta →
      ∀ᶠ n in atTop, ∀ x, |f n x - harmonic n x| < eta := by
  intro eta heta
  have hevent : ∀ᶠ n in atTop, eps n < eta :=
    heps (Iio_mem_nhds heta)
  filter_upwards [hevent] with n hn
  intro x
  exact lt_of_le_of_lt
    (fkIsingSquare_dirichlet_sandwich_stability n
      (upper n) (lower n) (harmonic n) (f n) (eps n)
      (hupper n) (hlower n) (hharmonic n)
      (hupperBoundary n) (hlowerBoundary n) (hsandwich n) x) hn

end

end StatMech.Universality
