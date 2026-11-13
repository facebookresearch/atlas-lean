/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerLaplacian
import Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerFaceLaplacian
import Code.Universality.IsingFermionicBoundaryRadialInterpolation











namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

private def centeredRadialHalf (i j : Nat) : Nat :=
  (i + j + 1) / 2

private theorem natAbs_le_of_int_bounds {n : Nat} {z : Int}
    (h0 : -(n : Int) <= z) (h1 : z <= (n : Int)) : z.natAbs <= n := by
  have h : |z| <= (n : Int) := abs_le.mpr ⟨h0, h1⟩
  rw [Int.abs_eq_natAbs] at h
  exact_mod_cast h


def fkIsingSquareCenteredRadialPatchVertex
    (n : Nat) (i j : Fin (2 * n)) : (fkSquareBoxPlanar n).V := by
  let q := centeredRadialHalf i.1 j.1
  refine ⟨![(q : Int) - (n : Int), (i.1 : Int) - (q : Int)], ?_⟩
  intro k
  fin_cases k
  · change ((q : Int) - (n : Int)).natAbs <= n
    apply natAbs_le_of_int_bounds
    · dsimp only [q, centeredRadialHalf]
      have hi := i.2
      have hj := j.2
      omega
    · dsimp only [q, centeredRadialHalf]
      have hi := i.2
      have hj := j.2
      omega
  · change ((i.1 : Int) - (q : Int)).natAbs <= n
    apply natAbs_le_of_int_bounds
    · dsimp only [q, centeredRadialHalf]
      have hi := i.2
      have hj := j.2
      omega
    · dsimp only [q, centeredRadialHalf]
      have hi := i.2
      have hj := j.2
      omega


def fkIsingSquareCenteredRadialPatchDirection (i j : Nat) :
    FKIsingSquareDirection :=
  if Even (i + j) then .east else .north

theorem fkIsingSquareCenteredRadialPatchDirection_available
    (n : Nat) (i j : Fin (2 * n)) :
    fkIsingSquareDirectionAvailable n
      (fkIsingSquareCenteredRadialPatchVertex n i j)
      (fkIsingSquareCenteredRadialPatchDirection i.1 j.1) := by
  have hi := i.2
  have hj := j.2
  by_cases h : Even (i.1 + j.1)
  · simp [fkIsingSquareCenteredRadialPatchDirection, h,
      fkIsingSquareDirectionAvailable,
      fkIsingSquareCenteredRadialPatchVertex, centeredRadialHalf]
    omega
  · simp [fkIsingSquareCenteredRadialPatchDirection, h,
      fkIsingSquareDirectionAvailable,
      fkIsingSquareCenteredRadialPatchVertex, centeredRadialHalf]
    omega


def fkIsingSquareCenteredRadialPatchEdge
    (n : Nat) (i j : Fin (2 * n)) :
    FKIsingMedialVertex (fkSquareBoxPlanar n) :=
  fkIsingSquareDirectionEdge n
    (fkIsingSquareCenteredRadialPatchVertex n i j)
    (fkIsingSquareCenteredRadialPatchDirection i.1 j.1)
    (fkIsingSquareCenteredRadialPatchDirection_available n i j)

theorem fkIsingSquareCenteredRadialPatchEdge_eq_east
    (n : Nat) (i j : Fin (2 * n)) (h : Even (i.1 + j.1)) :
    fkIsingSquareCenteredRadialPatchEdge n i j =
      fkIsingSquareDirectionEdge n
        (fkIsingSquareCenteredRadialPatchVertex n i j) .east
        (by simpa [fkIsingSquareCenteredRadialPatchDirection, h] using
          fkIsingSquareCenteredRadialPatchDirection_available n i j) := by
  unfold fkIsingSquareCenteredRadialPatchEdge
  simp only [fkIsingSquareCenteredRadialPatchDirection, if_pos h]

theorem fkIsingSquareCenteredRadialPatchEdge_eq_north
    (n : Nat) (i j : Fin (2 * n)) (h : ¬ Even (i.1 + j.1)) :
    fkIsingSquareCenteredRadialPatchEdge n i j =
      fkIsingSquareDirectionEdge n
        (fkIsingSquareCenteredRadialPatchVertex n i j) .north
        (by simpa [fkIsingSquareCenteredRadialPatchDirection, h] using
          fkIsingSquareCenteredRadialPatchDirection_available n i j) := by
  unfold fkIsingSquareCenteredRadialPatchEdge
  simp only [fkIsingSquareCenteredRadialPatchDirection, if_neg h]



theorem fkIsingSquareCenteredRadialPatchEdge_add_side_eq_radialPatchEdge
    (n m a b : Nat) (hm : m ≤ n) (ha : a < m) (hb : b < m) :
    fkIsingSquareCenteredRadialPatchEdge n
        ⟨n + a, by omega⟩ ⟨n + b, by omega⟩ =
      fkIsingSquareRadialPatchEdge n m hm
        ⟨a, ha⟩ ⟨b, hb⟩ := by
  have hhalf : centeredRadialHalf (n + a) (n + b) =
      n + (a + b + 1) / 2 := by
    simp [centeredRadialHalf]
    omega
  have hv : fkIsingSquareCenteredRadialPatchVertex n
        ⟨n + a, by omega⟩ ⟨n + b, by omega⟩ =
      fkIsingSquareRadialPatchVertex n m hm ⟨a, ha⟩ ⟨b, hb⟩ := by
    apply Subtype.ext
    funext k
    fin_cases k
    · change ((centeredRadialHalf (n + a) (n + b) : Int) - (n : Int)) =
          ((a + b + 1) / 2 : Int)
      rw [hhalf]
      omega
    · change ((n + a : Nat) : Int) -
          (centeredRadialHalf (n + a) (n + b) : Int) =
        (a : Int) - ((a + b + 1) / 2 : Int)
      rw [hhalf]
      omega
  have heven : Even (n + a + (n + b)) ↔ Even (a + b) := by
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c - n, ?_⟩
      omega
    · rintro ⟨c, hc⟩
      refine ⟨n + c, ?_⟩
      omega
  have hd : fkIsingSquareCenteredRadialPatchDirection
        (n + a) (n + b) = fkIsingSquareRadialPatchDirection a b := by
    simp [fkIsingSquareCenteredRadialPatchDirection,
      fkIsingSquareRadialPatchDirection, heven]
  unfold fkIsingSquareCenteredRadialPatchEdge fkIsingSquareRadialPatchEdge
  simpa only [hv, hd]


def isingCenteredRadialGridPosition
    (mesh : Real) (n i j : Nat) : Complex :=
  isingRadialGridPosition mesh i j - (mesh * n : Real)


def isingReflectedCenteredRadialGridPosition
    (mesh : Real) (n i j : Nat) : Complex :=
  (starRingEnd Complex) (isingCenteredRadialGridPosition mesh n i j)



theorem isingReflectedCenteredRadialGridPosition_eq
    (mesh : Real) (n i j : Nat) :
    isingReflectedCenteredRadialGridPosition mesh n i j =
      (mesh * (((i : Real) + (j : Real) + 1) / 2 - n) : Real) +
        (mesh * (((j : Real) - (i : Real)) / 2) : Real) * Complex.I := by
  apply Complex.ext <;>
    simp [isingReflectedCenteredRadialGridPosition,
      isingCenteredRadialGridPosition, isingRadialGridPosition,
      Complex.mul_re, Complex.mul_im] <;>
    ring

theorem isingReflectedCenteredRadialGridPosition_succ_i
    (mesh : Real) (n i j : Nat) :
    isingReflectedCenteredRadialGridPosition mesh n (i + 1) j =
      isingReflectedCenteredRadialGridPosition mesh n i j +
        (mesh : Complex) / 2 * (1 - Complex.I) := by
  apply Complex.ext <;>
    simp [isingReflectedCenteredRadialGridPosition,
      isingCenteredRadialGridPosition, isingRadialGridPosition,
      Complex.mul_re, Complex.mul_im] <;>
    ring

theorem isingReflectedCenteredRadialGridPosition_succ_j
    (mesh : Real) (n i j : Nat) :
    isingReflectedCenteredRadialGridPosition mesh n i (j + 1) =
      isingReflectedCenteredRadialGridPosition mesh n i j +
        (mesh : Complex) / 2 * (1 + Complex.I) := by
  apply Complex.ext <;>
    simp [isingReflectedCenteredRadialGridPosition,
      isingCenteredRadialGridPosition, isingRadialGridPosition,
      Complex.mul_re, Complex.mul_im] <;>
    ring



theorem isingReflectedCenteredRadialGridPosition_succ_both
    (mesh : Real) (n i j : Nat) :
    isingReflectedCenteredRadialGridPosition mesh n (i + 1) (j + 1) =
      isingReflectedCenteredRadialGridPosition mesh n i j + mesh := by
  rw [isingReflectedCenteredRadialGridPosition_succ_j,
    isingReflectedCenteredRadialGridPosition_succ_i]
  ring



theorem isingReflectedCenteredRadialGridPosition_vertical_macroStep
    (mesh : Real) (n i j : Nat) :
    isingReflectedCenteredRadialGridPosition mesh n i (j + 1) =
      isingReflectedCenteredRadialGridPosition mesh n (i + 1) j +
        mesh * Complex.I := by
  rw [isingReflectedCenteredRadialGridPosition_succ_j,
    isingReflectedCenteredRadialGridPosition_succ_i]
  ring

theorem isingReflectedCenteredRadialGridPosition_diagonal_add
    (mesh : Real) (n i j k : Nat) :
    isingReflectedCenteredRadialGridPosition mesh n (i + k) (j + k) =
      isingReflectedCenteredRadialGridPosition mesh n i j +
        (k : Real) * mesh := by
  rw [isingReflectedCenteredRadialGridPosition_eq,
    isingReflectedCenteredRadialGridPosition_eq]
  push_cast
  ring

theorem isingReflectedCenteredRadialGridPosition_antidiagonal_add
    (mesh : Real) (n i j N k : Nat) (hk : k ≤ N) :
    isingReflectedCenteredRadialGridPosition mesh n
        (i + (N - k)) (j + k) =
      isingReflectedCenteredRadialGridPosition mesh n (i + N) j +
        ((k : Real) * mesh) * Complex.I := by
  rw [isingReflectedCenteredRadialGridPosition_eq,
    isingReflectedCenteredRadialGridPosition_eq]
  push_cast [Nat.cast_sub hk]
  ring

theorem isingReflectedCenteredRadialGridPosition_diagonal_sub
    (mesh : Real) (n i j N M k : Nat) (hkN : k ≤ N) (hkM : k ≤ M) :
    isingReflectedCenteredRadialGridPosition mesh n
        (i + (N - k)) (j + (M - k)) =
      isingReflectedCenteredRadialGridPosition mesh n (i + N) (j + M) -
        (k : Real) * mesh := by
  rw [isingReflectedCenteredRadialGridPosition_eq,
    isingReflectedCenteredRadialGridPosition_eq]
  push_cast [Nat.cast_sub hkN, Nat.cast_sub hkM]
  ring

theorem isingReflectedCenteredRadialGridPosition_antidiagonal_sub
    (mesh : Real) (n i j N k : Nat) (hk : k ≤ N) :
    isingReflectedCenteredRadialGridPosition mesh n
        (i + k) (j + (N - k)) =
      isingReflectedCenteredRadialGridPosition mesh n i (j + N) -
        ((k : Real) * mesh) * Complex.I := by
  rw [isingReflectedCenteredRadialGridPosition_eq,
    isingReflectedCenteredRadialGridPosition_eq]
  push_cast [Nat.cast_sub hk]
  ring



theorem isingCenteredRadialGridPosition_eq_scaledCarrierPosition
    (n : Nat) (hn : 0 < n) (mesh : Real) (i j : Fin (2 * n))
    (s : FKIsingMedialSide) :
    isingCenteredRadialGridPosition mesh n i.1 j.1 =
      (mesh : Complex) * fkIsingSquareWiredCarrierPosition n hn
        (.dart (fkIsingSquareCenteredRadialPatchEdge n i j, s)) := by
  unfold isingCenteredRadialGridPosition isingRadialGridPosition
  change _ = (mesh : Complex) *
    ((fkIsingSquareSitePosition
      (fkIsingSquareOrientedEdge n
        (fkIsingSquareCenteredRadialPatchEdge n i j)).tail.1 +
      fkIsingSquareSitePosition
      (fkIsingSquareOrientedEdge n
        (fkIsingSquareCenteredRadialPatchEdge n i j)).head.1) / 2)
  by_cases h : Even (i.1 + j.1)
  · rw [fkIsingSquareCenteredRadialPatchEdge_eq_east n i j h,
      fkIsingSquareOrientedEdge_directionEdge]
    simp [fkIsingSquareDirectionEdgeOrientation, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareSitePosition,
      fkIsingSquareCenteredRadialPatchVertex, centeredRadialHalf,
      Complex.ext_iff]
    have hmod := Nat.even_iff.mp h
    have hqNat : 2 * ((i.1 + j.1 + 1) / 2) = i.1 + j.1 := by omega
    have hq : (2 : Real) * (((i.1 + j.1 + 1) / 2 : Nat) : Real) =
        (i.1 : Real) + (j.1 : Real) := by exact_mod_cast hqNat
    have hreal : ((i.1 : Real) + (j.1 : Real) + 1) / 2 =
        (((i.1 + j.1 + 1) / 2 : Nat) : Real) + 1 / 2 := by
      linarith
    have him : ((i.1 : Real) - (j.1 : Real)) / 2 =
        (i.1 : Real) - (((i.1 + j.1 + 1) / 2 : Nat) : Real) := by
      linarith
    have hdivInt :
        ((i.1 : Int) + (j.1 : Int) + 1) / 2 =
          (((i.1 + j.1 + 1) / 2 : Nat) : Int) := by
      omega
    have hdivReal :
        ((((i.1 : Int) + (j.1 : Int) + 1) / 2 : Int) : Real) =
          (((i.1 + j.1 + 1) / 2 : Nat) : Real) := by
      norm_cast
    constructor
    · rw [hreal]
      rw [hdivReal]
      ring
    · left
      exact him
  · rw [fkIsingSquareCenteredRadialPatchEdge_eq_north n i j h,
      fkIsingSquareOrientedEdge_directionEdge]
    simp [fkIsingSquareDirectionEdgeOrientation, fkIsingSquareNeighbor,
      fkIsingSquareNeighborSite, fkIsingSquareSitePosition,
      fkIsingSquareCenteredRadialPatchVertex, centeredRadialHalf,
      Complex.ext_iff]
    have hmod := Nat.not_even_iff.mp h
    have hqNat : 2 * ((i.1 + j.1 + 1) / 2) = i.1 + j.1 + 1 := by omega
    have hq : (2 : Real) * (((i.1 + j.1 + 1) / 2 : Nat) : Real) =
        (i.1 : Real) + (j.1 : Real) + 1 := by exact_mod_cast hqNat
    have hreal : ((i.1 : Real) + (j.1 : Real) + 1) / 2 =
        (((i.1 + j.1 + 1) / 2 : Nat) : Real) := by
      linarith
    have him : (i.1 : Real) - (j.1 : Real) =
        ((i.1 : Real) - (((i.1 + j.1 + 1) / 2 : Nat) : Real)) +
          ((i.1 : Real) - (((i.1 + j.1 + 1) / 2 : Nat) : Real) + 1) := by
      linarith
    have hdivInt :
        ((i.1 : Int) + (j.1 : Int) + 1) / 2 =
          (((i.1 + j.1 + 1) / 2 : Nat) : Int) := by
      omega
    have hdivReal :
        ((((i.1 : Int) + (j.1 : Int) + 1) / 2 : Int) : Real) =
          (((i.1 + j.1 + 1) / 2 : Nat) : Real) := by
      norm_cast
    constructor
    · rw [hreal]
      rw [hdivReal]
      ring
    · left
      exact him


noncomputable def fkIsingSquareBoundaryCenteredRadialPatchFullObservable
    (n : Nat) (hn : 0 < n) (i j : Fin (2 * n)) : Complex :=
  fkIsingSquareBoundaryFullMedialObservable n hn
    (fkIsingSquareCenteredRadialPatchEdge n i j)


noncomputable def fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension
    (n : Nat) (hn : 0 < n) : Nat -> Nat -> Complex := fun i j =>
  if hi : i < 2 * n then
    if hj : j < 2 * n then
      fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨i, hi⟩ ⟨j, hj⟩
    else 0
  else 0

@[simp] theorem
    fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension_apply
    (n : Nat) (hn : 0 < n) (i j : Nat)
    (hi : i < 2 * n) (hj : j < 2 * n) :
    fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension n hn i j =
      fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨i, hi⟩ ⟨j, hj⟩ := by
  simp [fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension,
    hi, hj]

private theorem centeredRadialPatchVertex_strictInterior
    (n I J : Nat)
    (hI0 : 0 < I) (hI1 : I + 1 < 2 * n)
    (hJ0 : 0 < J) (hJ1 : J + 1 < 2 * n) :
    let x := fkIsingSquareCenteredRadialPatchVertex n
      ⟨I, by omega⟩ ⟨J, by omega⟩
    fkIsingSquareDirectionAvailable n x .east ∧
      fkIsingSquareDirectionAvailable n x .north ∧
      fkIsingSquareDirectionAvailable n x .west ∧
      fkIsingSquareDirectionAvailable n x .south := by
  dsimp
  simp [fkIsingSquareDirectionAvailable,
    fkIsingSquareCenteredRadialPatchVertex, centeredRadialHalf]
  constructor
  · omega
  constructor
  · omega
  constructor <;> omega



theorem fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad
    (n I J : Nat) (hn : 0 < n)
    (hI0 : 0 < I) (hI1 : I + 1 < 2 * n)
    (hJ0 : 0 < J) (hJ1 : J + 1 < 2 * n)
    (heven : Even (I + J)) :
    IsingSquareSHolomorphicQuad
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨I - 1, by omega⟩ ⟨J, by omega⟩)
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨I - 1, by omega⟩ ⟨J - 1, by omega⟩)
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨I, by omega⟩ ⟨J - 1, by omega⟩)
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨I, by omega⟩ ⟨J, by omega⟩) := by
  let ii : Fin (2 * n) := ⟨I, by omega⟩
  let jj : Fin (2 * n) := ⟨J, by omega⟩
  let x := fkIsingSquareCenteredRadialPatchVertex n ii jj
  obtain ⟨heast, hnorth, hwest, hsouth⟩ :=
    centeredRadialPatchVertex_strictInterior n I J hI0 hI1 hJ0 hJ1
  have hquad := fkIsingSquareBoundaryFullVertexFullObservable_quad
    n hn x heast hnorth hwest hsouth
  change IsingSquareSHolomorphicQuad
    (fkIsingSquareBoundaryFullMedialObservable n hn
      (fkIsingSquareDirectionEdge n x .south hsouth))
    (fkIsingSquareBoundaryFullMedialObservable n hn
      (fkIsingSquareDirectionEdge n x .west hwest))
    (fkIsingSquareBoundaryFullMedialObservable n hn
      (fkIsingSquareDirectionEdge n x .north hnorth))
    (fkIsingSquareBoundaryFullMedialObservable n hn
      (fkIsingSquareDirectionEdge n x .east heast)) at hquad
  have hoddS : ¬ Even (I - 1 + J) := by
    rw [Nat.not_even_iff]
    have hmod := Nat.even_iff.mp heven
    omega
  have hS : fkIsingSquareCenteredRadialPatchEdge n
        ⟨I - 1, by omega⟩ ⟨J, by omega⟩ =
      fkIsingSquareDirectionEdge n x .south hsouth := by
    rw [fkIsingSquareCenteredRadialPatchEdge_eq_north n _ _ hoddS]
    apply Subtype.ext
    simp only [fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    right
    constructor <;> apply Subtype.ext <;> funext k <;> fin_cases k <;>
      simp [x, ii, jj, fkIsingSquareCenteredRadialPatchVertex,
        centeredRadialHalf, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;>
      have hmod := Nat.even_iff.mp heven <;> omega
  have hevenW : Even (I - 1 + (J - 1)) := by
    rw [Nat.even_iff]
    have hmod := Nat.even_iff.mp heven
    omega
  have hW : fkIsingSquareCenteredRadialPatchEdge n
        ⟨I - 1, by omega⟩ ⟨J - 1, by omega⟩ =
      fkIsingSquareDirectionEdge n x .west hwest := by
    rw [fkIsingSquareCenteredRadialPatchEdge_eq_east n _ _ hevenW]
    apply Subtype.ext
    simp only [fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    right
    constructor <;> apply Subtype.ext <;> funext k <;> fin_cases k <;>
      simp [x, ii, jj, fkIsingSquareCenteredRadialPatchVertex,
        centeredRadialHalf, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;>
      have hmod := Nat.even_iff.mp heven <;> omega
  have hoddN : ¬ Even (I + (J - 1)) := by
    rw [Nat.not_even_iff]
    have hmod := Nat.even_iff.mp heven
    omega
  have hN : fkIsingSquareCenteredRadialPatchEdge n
        ⟨I, by omega⟩ ⟨J - 1, by omega⟩ =
      fkIsingSquareDirectionEdge n x .north hnorth := by
    rw [fkIsingSquareCenteredRadialPatchEdge_eq_north n _ _ hoddN]
    apply Subtype.ext
    simp only [fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    left
    constructor <;> apply Subtype.ext <;> funext k <;> fin_cases k <;>
      simp [x, ii, jj, fkIsingSquareCenteredRadialPatchVertex,
        centeredRadialHalf, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;>
      have hmod := Nat.even_iff.mp heven <;> omega
  have hE : fkIsingSquareCenteredRadialPatchEdge n
        ⟨I, by omega⟩ ⟨J, by omega⟩ =
      fkIsingSquareDirectionEdge n x .east heast := by
    rw [fkIsingSquareCenteredRadialPatchEdge_eq_east n _ _ heven]
  simpa only [fkIsingSquareBoundaryCenteredRadialPatchFullObservable,
    hS, hW, hN, hE] using hquad




theorem fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_of_even_available
    (n I J : Nat) (hn : 0 < n)
    (hI0 : 0 < I) (hI : I < 2 * n)
    (hJ0 : 0 < J) (hJ : J < 2 * n)
    (heven : Even (I + J))
    (heast : fkIsingSquareDirectionAvailable n
      (fkIsingSquareCenteredRadialPatchVertex n
        ⟨I, hI⟩ ⟨J, hJ⟩) .east)
    (hnorth : fkIsingSquareDirectionAvailable n
      (fkIsingSquareCenteredRadialPatchVertex n
        ⟨I, hI⟩ ⟨J, hJ⟩) .north)
    (hwest : fkIsingSquareDirectionAvailable n
      (fkIsingSquareCenteredRadialPatchVertex n
        ⟨I, hI⟩ ⟨J, hJ⟩) .west)
    (hsouth : fkIsingSquareDirectionAvailable n
      (fkIsingSquareCenteredRadialPatchVertex n
        ⟨I, hI⟩ ⟨J, hJ⟩) .south) :
    IsingSquareSHolomorphicQuad
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨I - 1, by omega⟩ ⟨J, hJ⟩)
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨I - 1, by omega⟩ ⟨J - 1, by omega⟩)
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨I, hI⟩ ⟨J - 1, by omega⟩)
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨I, hI⟩ ⟨J, hJ⟩) := by
  let ii : Fin (2 * n) := ⟨I, hI⟩
  let jj : Fin (2 * n) := ⟨J, hJ⟩
  let x := fkIsingSquareCenteredRadialPatchVertex n ii jj
  have hquad := fkIsingSquareBoundaryFullVertexFullObservable_quad
    n hn x heast hnorth hwest hsouth
  change IsingSquareSHolomorphicQuad
    (fkIsingSquareBoundaryFullMedialObservable n hn
      (fkIsingSquareDirectionEdge n x .south hsouth))
    (fkIsingSquareBoundaryFullMedialObservable n hn
      (fkIsingSquareDirectionEdge n x .west hwest))
    (fkIsingSquareBoundaryFullMedialObservable n hn
      (fkIsingSquareDirectionEdge n x .north hnorth))
    (fkIsingSquareBoundaryFullMedialObservable n hn
      (fkIsingSquareDirectionEdge n x .east heast)) at hquad
  have hoddS : ¬ Even (I - 1 + J) := by
    rw [Nat.not_even_iff]
    have hmod := Nat.even_iff.mp heven
    omega
  have hS : fkIsingSquareCenteredRadialPatchEdge n
        ⟨I - 1, by omega⟩ ⟨J, hJ⟩ =
      fkIsingSquareDirectionEdge n x .south hsouth := by
    rw [fkIsingSquareCenteredRadialPatchEdge_eq_north n _ _ hoddS]
    apply Subtype.ext
    simp only [fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    right
    constructor <;> apply Subtype.ext <;> funext k <;> fin_cases k <;>
      simp [x, ii, jj, fkIsingSquareCenteredRadialPatchVertex,
        centeredRadialHalf, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;>
      have hmod := Nat.even_iff.mp heven <;> omega
  have hevenW : Even (I - 1 + (J - 1)) := by
    rw [Nat.even_iff]
    have hmod := Nat.even_iff.mp heven
    omega
  have hW : fkIsingSquareCenteredRadialPatchEdge n
        ⟨I - 1, by omega⟩ ⟨J - 1, by omega⟩ =
      fkIsingSquareDirectionEdge n x .west hwest := by
    rw [fkIsingSquareCenteredRadialPatchEdge_eq_east n _ _ hevenW]
    apply Subtype.ext
    simp only [fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    right
    constructor <;> apply Subtype.ext <;> funext k <;> fin_cases k <;>
      simp [x, ii, jj, fkIsingSquareCenteredRadialPatchVertex,
        centeredRadialHalf, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;>
      have hmod := Nat.even_iff.mp heven <;> omega
  have hoddN : ¬ Even (I + (J - 1)) := by
    rw [Nat.not_even_iff]
    have hmod := Nat.even_iff.mp heven
    omega
  have hN : fkIsingSquareCenteredRadialPatchEdge n
        ⟨I, hI⟩ ⟨J - 1, by omega⟩ =
      fkIsingSquareDirectionEdge n x .north hnorth := by
    rw [fkIsingSquareCenteredRadialPatchEdge_eq_north n _ _ hoddN]
    apply Subtype.ext
    simp only [fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    left
    constructor <;> apply Subtype.ext <;> funext k <;> fin_cases k <;>
      simp [x, ii, jj, fkIsingSquareCenteredRadialPatchVertex,
        centeredRadialHalf, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;>
      have hmod := Nat.even_iff.mp heven <;> omega
  have hE : fkIsingSquareCenteredRadialPatchEdge n
        ⟨I, hI⟩ ⟨J, hJ⟩ =
      fkIsingSquareDirectionEdge n x .east heast := by
    rw [fkIsingSquareCenteredRadialPatchEdge_eq_east n _ _ heven]
  simpa only [fkIsingSquareBoundaryCenteredRadialPatchFullObservable,
    hS, hW, hN, hE] using hquad




theorem fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_right_of_even
    (n J : Nat) (hn : 0 < n) (hJ0 : 0 < J) (hJ : J < 2 * n)
    (heven : Even ((2 * n - 1) + J)) :
    IsingSquareSHolomorphicQuad
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨2 * n - 2, by omega⟩ ⟨J, hJ⟩)
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨2 * n - 2, by omega⟩ ⟨J - 1, by omega⟩)
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨2 * n - 1, by omega⟩ ⟨J - 1, by omega⟩)
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨2 * n - 1, by omega⟩ ⟨J, hJ⟩) := by
  apply
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_of_even_available
      n (2 * n - 1) J hn (by omega) (by omega) hJ0 hJ heven <;>
    simp [fkIsingSquareDirectionAvailable,
      fkIsingSquareCenteredRadialPatchVertex, centeredRadialHalf] <;>
    have hmod := Nat.even_iff.mp heven <;> omega




theorem fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_top_of_even
    (n I : Nat) (hn : 0 < n) (hI0 : 0 < I) (hI : I < 2 * n)
    (heven : Even (I + (2 * n - 1))) :
    IsingSquareSHolomorphicQuad
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨I - 1, by omega⟩ ⟨2 * n - 1, by omega⟩)
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨I - 1, by omega⟩ ⟨2 * n - 2, by omega⟩)
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨I, hI⟩ ⟨2 * n - 2, by omega⟩)
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨I, hI⟩ ⟨2 * n - 1, by omega⟩) := by
  apply
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_of_even_available
      n I (2 * n - 1) hn hI0 hI (by omega) (by omega) heven <;>
    simp [fkIsingSquareDirectionAvailable,
      fkIsingSquareCenteredRadialPatchVertex, centeredRadialHalf] <;>
    have hmod := Nat.even_iff.mp heven <;> omega

private def centeredRadialPatchDualFullFace
    (n I J : Nat)
    (hI0 : 0 < I) (hI1 : I + 1 < 2 * n)
    (hJ0 : 0 < J) (hJ1 : J + 1 < 2 * n)
    (hodd : ¬ Even (I + J)) : FKIsingSquareFullFaceNode n := by
  let q := centeredRadialHalf I J
  have hmod := Nat.not_even_iff.mp hodd
  refine (⟨q - 1, ?_⟩, ⟨n + I - q, ?_⟩)
  · dsimp only [q, centeredRadialHalf]
    omega
  · dsimp only [q, centeredRadialHalf]
    omega

private theorem centeredRadialPatchDualFullFace_bounds
    (n I J : Nat)
    (hI0 : 0 < I) (hI1 : I + 1 < 2 * n)
    (hJ0 : 0 < J) (hJ1 : J + 1 < 2 * n)
    (hodd : ¬ Even (I + J)) :
    let c := centeredRadialPatchDualFullFace n I J
      hI0 hI1 hJ0 hJ1 hodd
    0 < c.1.1 ∧ c.1.1 + 1 < 2 * n ∧
      0 < c.2.1 ∧ c.2.1 + 1 < 2 * n := by
  dsimp [centeredRadialPatchDualFullFace, centeredRadialHalf]
  have hmod := Nat.not_even_iff.mp hodd
  omega



theorem fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_of_odd
    (n I J : Nat) (hn : 0 < n)
    (hI0 : 0 < I) (hI1 : I + 1 < 2 * n)
    (hJ0 : 0 < J) (hJ1 : J + 1 < 2 * n)
    (hodd : ¬ Even (I + J)) :
    IsingSquareSHolomorphicQuad
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨I, by omega⟩ ⟨J - 1, by omega⟩)
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨I, by omega⟩ ⟨J, by omega⟩)
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨I - 1, by omega⟩ ⟨J, by omega⟩)
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨I - 1, by omega⟩ ⟨J - 1, by omega⟩) := by
  let c := centeredRadialPatchDualFullFace n I J
    hI0 hI1 hJ0 hJ1 hodd
  have hevenN : Even (I + (J - 1)) := by
    rw [Nat.even_iff]
    have hmod := Nat.not_even_iff.mp hodd
    omega
  have hN : fkIsingSquareCenteredRadialPatchEdge n
        ⟨I, by omega⟩ ⟨J - 1, by omega⟩ = faceNorthEdge n c := by
    rw [fkIsingSquareCenteredRadialPatchEdge_eq_east n _ _ hevenN]
    apply Subtype.ext
    simp only [faceNorthEdge, fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    left
    constructor <;> apply Subtype.ext <;> funext k <;> fin_cases k <;>
      simp [c, centeredRadialPatchDualFullFace, faceNWVertex,
        fkIsingSquareCenteredRadialPatchVertex, centeredRadialHalf,
        fkIsingSquareInteriorCellKey, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;>
      have hmod := Nat.not_even_iff.mp hodd <;> omega
  have hE : fkIsingSquareCenteredRadialPatchEdge n
        ⟨I, by omega⟩ ⟨J, by omega⟩ = faceEastEdge n c := by
    rw [fkIsingSquareCenteredRadialPatchEdge_eq_north n _ _ hodd]
    apply Subtype.ext
    simp only [faceEastEdge, fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    left
    constructor <;> apply Subtype.ext <;> funext k <;> fin_cases k <;>
      simp [c, centeredRadialPatchDualFullFace, faceSEVertex,
        fkIsingSquareCenteredRadialPatchVertex, centeredRadialHalf,
        fkIsingSquareInteriorCellKey, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;>
      have hmod := Nat.not_even_iff.mp hodd <;> omega
  have hevenS : Even (I - 1 + J) := by
    rw [Nat.even_iff]
    have hmod := Nat.not_even_iff.mp hodd
    omega
  have hS : fkIsingSquareCenteredRadialPatchEdge n
        ⟨I - 1, by omega⟩ ⟨J, by omega⟩ = faceSouthEdge n c := by
    rw [fkIsingSquareCenteredRadialPatchEdge_eq_east n _ _ hevenS]
    apply Subtype.ext
    simp only [faceSouthEdge, fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    left
    constructor <;> apply Subtype.ext <;> funext k <;> fin_cases k <;>
      simp [c, centeredRadialPatchDualFullFace, faceSWVertex,
        fkIsingSquareCenteredRadialPatchVertex, centeredRadialHalf,
        fkIsingSquareInteriorCellKey, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;>
      have hmod := Nat.not_even_iff.mp hodd <;> omega
  have hoddW : ¬ Even (I - 1 + (J - 1)) := by
    rw [Nat.not_even_iff]
    have hmod := Nat.not_even_iff.mp hodd
    omega
  have hW : fkIsingSquareCenteredRadialPatchEdge n
        ⟨I - 1, by omega⟩ ⟨J - 1, by omega⟩ = faceWestEdge n c := by
    rw [fkIsingSquareCenteredRadialPatchEdge_eq_north n _ _ hoddW]
    apply Subtype.ext
    simp only [faceWestEdge, fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    left
    constructor <;> apply Subtype.ext <;> funext k <;> fin_cases k <;>
      simp [c, centeredRadialPatchDualFullFace, faceSWVertex,
        fkIsingSquareCenteredRadialPatchVertex, centeredRadialHalf,
        fkIsingSquareInteriorCellKey, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;>
      have hmod := Nat.not_even_iff.mp hodd <;> omega
  obtain ⟨hwest, heast, hsouth, hnorth⟩ :=
    centeredRadialPatchDualFullFace_bounds n I J
      hI0 hI1 hJ0 hJ1 hodd
  have hSWwest : fkIsingSquareDirectionAvailable n (faceSWVertex n c) .west := by
    change -(n : Int) < (fkIsingSquareInteriorCellKey n c).1
    simp [fkIsingSquareInteriorCellKey] at hwest ⊢
    omega
  have hSWsouth : fkIsingSquareDirectionAvailable n (faceSWVertex n c) .south := by
    change -(n : Int) < (fkIsingSquareInteriorCellKey n c).2
    simp [fkIsingSquareInteriorCellKey] at hsouth ⊢
    omega
  have hNWwest : fkIsingSquareDirectionAvailable n (faceNWVertex n c) .west := by
    change -(n : Int) < (fkIsingSquareInteriorCellKey n c).1
    simp [fkIsingSquareInteriorCellKey] at hwest ⊢
    omega
  have hNWnorth : fkIsingSquareDirectionAvailable n (faceNWVertex n c) .north := by
    change (fkIsingSquareInteriorCellKey n c).2 + 1 < (n : Int)
    have hc : (c.2.1 : Int) + 1 < 2 * (n : Int) := by
      exact_mod_cast hnorth
    dsimp [fkIsingSquareInteriorCellKey]
    linarith
  have hSEeast : fkIsingSquareDirectionAvailable n (faceSEVertex n c) .east := by
    change (fkIsingSquareInteriorCellKey n c).1 + 1 < (n : Int)
    have hc : (c.1.1 : Int) + 1 < 2 * (n : Int) := by
      exact_mod_cast heast
    dsimp [fkIsingSquareInteriorCellKey]
    linarith
  have hSEsouth : fkIsingSquareDirectionAvailable n (faceSEVertex n c) .south := by
    change -(n : Int) < (fkIsingSquareInteriorCellKey n c).2
    simp [fkIsingSquareInteriorCellKey] at hsouth ⊢
    omega
  have hNWeast : fkIsingSquareDirectionAvailable n (faceNWVertex n c) .east := by
    simp [fkIsingSquareDirectionAvailable, faceNWVertex,
      fkIsingSquareInteriorCellKey] <;> omega
  have hNWsouth : fkIsingSquareDirectionAvailable n (faceNWVertex n c) .south := by
    simp [fkIsingSquareDirectionAvailable, faceNWVertex,
      fkIsingSquareInteriorCellKey]
  have hSEnorth : fkIsingSquareDirectionAvailable n (faceSEVertex n c) .north := by
    simp [fkIsingSquareDirectionAvailable, faceSEVertex,
      fkIsingSquareInteriorCellKey] <;> omega
  have hSEwest : fkIsingSquareDirectionAvailable n (faceSEVertex n c) .west := by
    simp [fkIsingSquareDirectionAvailable, faceSEVertex,
      fkIsingSquareInteriorCellKey]
  have hSWeast : fkIsingSquareDirectionAvailable n (faceSWVertex n c) .east := by
    simp [fkIsingSquareDirectionAvailable, faceSWVertex,
      fkIsingSquareInteriorCellKey] <;> omega
  have hSWnorth : fkIsingSquareDirectionAvailable n (faceSWVertex n c) .north := by
    simp [fkIsingSquareDirectionAvailable, faceSWVertex,
      fkIsingSquareInteriorCellKey] <;> omega
  have hnotN : (faceNorthEdge n c).1 ∉
      fkIsingSquarePerimeterPrimalEdgeFinset n := by
    simpa [faceNorthEdge] using
      fkIsingSquareDirectionEdge_not_mem_perimeter_of_interior n
        (faceNWVertex n c) .east hNWeast
        hNWeast hNWnorth hNWwest hNWsouth
  have hnotE : (faceEastEdge n c).1 ∉
      fkIsingSquarePerimeterPrimalEdgeFinset n := by
    simpa [faceEastEdge] using
      fkIsingSquareDirectionEdge_not_mem_perimeter_of_interior n
        (faceSEVertex n c) .north hSEnorth
        hSEeast hSEnorth hSEwest hSEsouth
  have hnotS : (faceSouthEdge n c).1 ∉
      fkIsingSquarePerimeterPrimalEdgeFinset n := by
    simpa [faceSouthEdge] using
      fkIsingSquareDirectionEdge_not_mem_perimeter_of_interior n
        (faceSWVertex n c) .east hSWeast
        hSWeast hSWnorth hSWwest hSWsouth
  have hnotW : (faceWestEdge n c).1 ∉
      fkIsingSquarePerimeterPrimalEdgeFinset n := by
    simpa [faceWestEdge] using
      fkIsingSquareDirectionEdge_not_mem_perimeter_of_interior n
        (faceSWVertex n c) .north hSWnorth
        hSWeast hSWnorth hSWwest hSWsouth
  have hquad := fkIsingSquareBoundaryFullFaceFullObservable_quad
    n hn c hnotN hnotE hnotS hnotW
  unfold fkIsingSquareBoundaryCenteredRadialPatchFullObservable
  rw [hN, hE, hS, hW]
  exact hquad

private def centeredRadialPatchDualFullFaceOfInterior
    (n I J : Nat)
    (hwest : 0 < centeredRadialHalf I J - 1)
    (heast : centeredRadialHalf I J - 1 + 1 < 2 * n)
    (hsouth : 0 < n + I - centeredRadialHalf I J)
    (hnorth : n + I - centeredRadialHalf I J + 1 < 2 * n) :
    FKIsingSquareFullFaceNode n := by
  refine (⟨centeredRadialHalf I J - 1, by omega⟩,
    ⟨n + I - centeredRadialHalf I J, by omega⟩)




theorem
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_of_odd_faceInterior
    (n I J : Nat) (hn : 0 < n)
    (hI0 : 0 < I) (hI : I < 2 * n)
    (hJ0 : 0 < J) (hJ : J < 2 * n)
    (hodd : ¬ Even (I + J))
    (hwest : 0 < centeredRadialHalf I J - 1)
    (heast : centeredRadialHalf I J - 1 + 1 < 2 * n)
    (hsouth : 0 < n + I - centeredRadialHalf I J)
    (hnorth : n + I - centeredRadialHalf I J + 1 < 2 * n) :
    IsingSquareSHolomorphicQuad
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨I, hI⟩ ⟨J - 1, by omega⟩)
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨I, hI⟩ ⟨J, hJ⟩)
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨I - 1, by omega⟩ ⟨J, hJ⟩)
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨I - 1, by omega⟩ ⟨J - 1, by omega⟩) := by
  let c := centeredRadialPatchDualFullFaceOfInterior n I J
    hwest heast hsouth hnorth
  have hevenN : Even (I + (J - 1)) := by
    rw [Nat.even_iff]
    have hmod := Nat.not_even_iff.mp hodd
    omega
  have hN : fkIsingSquareCenteredRadialPatchEdge n
        ⟨I, hI⟩ ⟨J - 1, by omega⟩ = faceNorthEdge n c := by
    rw [fkIsingSquareCenteredRadialPatchEdge_eq_east n _ _ hevenN]
    apply Subtype.ext
    simp only [faceNorthEdge, fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    left
    constructor <;> apply Subtype.ext <;> funext k <;> fin_cases k <;>
      simp [c, centeredRadialPatchDualFullFaceOfInterior, faceNWVertex,
        fkIsingSquareCenteredRadialPatchVertex, centeredRadialHalf,
        fkIsingSquareInteriorCellKey, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;>
      have hmod := Nat.not_even_iff.mp hodd <;> omega
  have hE : fkIsingSquareCenteredRadialPatchEdge n
        ⟨I, hI⟩ ⟨J, hJ⟩ = faceEastEdge n c := by
    rw [fkIsingSquareCenteredRadialPatchEdge_eq_north n _ _ hodd]
    apply Subtype.ext
    simp only [faceEastEdge, fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    left
    constructor <;> apply Subtype.ext <;> funext k <;> fin_cases k <;>
      simp [c, centeredRadialPatchDualFullFaceOfInterior, faceSEVertex,
        fkIsingSquareCenteredRadialPatchVertex, centeredRadialHalf,
        fkIsingSquareInteriorCellKey, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;>
      have hmod := Nat.not_even_iff.mp hodd <;> omega
  have hevenS : Even (I - 1 + J) := by
    rw [Nat.even_iff]
    have hmod := Nat.not_even_iff.mp hodd
    omega
  have hS : fkIsingSquareCenteredRadialPatchEdge n
        ⟨I - 1, by omega⟩ ⟨J, hJ⟩ = faceSouthEdge n c := by
    rw [fkIsingSquareCenteredRadialPatchEdge_eq_east n _ _ hevenS]
    apply Subtype.ext
    simp only [faceSouthEdge, fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    left
    constructor <;> apply Subtype.ext <;> funext k <;> fin_cases k <;>
      simp [c, centeredRadialPatchDualFullFaceOfInterior, faceSWVertex,
        fkIsingSquareCenteredRadialPatchVertex, centeredRadialHalf,
        fkIsingSquareInteriorCellKey, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;>
      have hmod := Nat.not_even_iff.mp hodd <;> omega
  have hoddW : ¬ Even (I - 1 + (J - 1)) := by
    rw [Nat.not_even_iff]
    have hmod := Nat.not_even_iff.mp hodd
    omega
  have hW : fkIsingSquareCenteredRadialPatchEdge n
        ⟨I - 1, by omega⟩ ⟨J - 1, by omega⟩ = faceWestEdge n c := by
    rw [fkIsingSquareCenteredRadialPatchEdge_eq_north n _ _ hoddW]
    apply Subtype.ext
    simp only [faceWestEdge, fkIsingSquareDirectionEdge]
    rw [Sym2.eq_iff]
    left
    constructor <;> apply Subtype.ext <;> funext k <;> fin_cases k <;>
      simp [c, centeredRadialPatchDualFullFaceOfInterior, faceSWVertex,
        fkIsingSquareCenteredRadialPatchVertex, centeredRadialHalf,
        fkIsingSquareInteriorCellKey, fkIsingSquareNeighbor,
        fkIsingSquareNeighborSite] <;>
      have hmod := Nat.not_even_iff.mp hodd <;> omega
  have hSWwest : fkIsingSquareDirectionAvailable n (faceSWVertex n c) .west := by
    change -(n : Int) < (fkIsingSquareInteriorCellKey n c).1
    simp [c, centeredRadialPatchDualFullFaceOfInterior,
      fkIsingSquareInteriorCellKey] at hwest ⊢
    omega
  have hSWsouth : fkIsingSquareDirectionAvailable n (faceSWVertex n c) .south := by
    change -(n : Int) < (fkIsingSquareInteriorCellKey n c).2
    simp [c, centeredRadialPatchDualFullFaceOfInterior,
      fkIsingSquareInteriorCellKey] at hsouth ⊢
    omega
  have hNWwest : fkIsingSquareDirectionAvailable n (faceNWVertex n c) .west := by
    change -(n : Int) < (fkIsingSquareInteriorCellKey n c).1
    simp [c, centeredRadialPatchDualFullFaceOfInterior,
      fkIsingSquareInteriorCellKey] at hwest ⊢
    omega
  have hNWnorth : fkIsingSquareDirectionAvailable n (faceNWVertex n c) .north := by
    change (fkIsingSquareInteriorCellKey n c).2 + 1 < (n : Int)
    have hc : (c.2.1 : Int) + 1 < 2 * (n : Int) := by
      exact_mod_cast hnorth
    dsimp [fkIsingSquareInteriorCellKey]
    linarith
  have hSEeast : fkIsingSquareDirectionAvailable n (faceSEVertex n c) .east := by
    change (fkIsingSquareInteriorCellKey n c).1 + 1 < (n : Int)
    have hc : (c.1.1 : Int) + 1 < 2 * (n : Int) := by
      exact_mod_cast heast
    dsimp [fkIsingSquareInteriorCellKey]
    linarith
  have hSEsouth : fkIsingSquareDirectionAvailable n (faceSEVertex n c) .south := by
    change -(n : Int) < (fkIsingSquareInteriorCellKey n c).2
    simp [c, centeredRadialPatchDualFullFaceOfInterior,
      fkIsingSquareInteriorCellKey] at hsouth ⊢
    omega
  have hNWeast : fkIsingSquareDirectionAvailable n (faceNWVertex n c) .east := by
    simp [fkIsingSquareDirectionAvailable, faceNWVertex,
      fkIsingSquareInteriorCellKey] <;> omega
  have hNWsouth : fkIsingSquareDirectionAvailable n (faceNWVertex n c) .south := by
    simp [fkIsingSquareDirectionAvailable, faceNWVertex,
      fkIsingSquareInteriorCellKey]
  have hSEnorth : fkIsingSquareDirectionAvailable n (faceSEVertex n c) .north := by
    simp [fkIsingSquareDirectionAvailable, faceSEVertex,
      fkIsingSquareInteriorCellKey] <;> omega
  have hSEwest : fkIsingSquareDirectionAvailable n (faceSEVertex n c) .west := by
    simp [fkIsingSquareDirectionAvailable, faceSEVertex,
      fkIsingSquareInteriorCellKey]
  have hSWeast : fkIsingSquareDirectionAvailable n (faceSWVertex n c) .east := by
    simp [fkIsingSquareDirectionAvailable, faceSWVertex,
      fkIsingSquareInteriorCellKey] <;> omega
  have hSWnorth : fkIsingSquareDirectionAvailable n (faceSWVertex n c) .north := by
    simp [fkIsingSquareDirectionAvailable, faceSWVertex,
      fkIsingSquareInteriorCellKey] <;> omega
  have hnotN : (faceNorthEdge n c).1 ∉
      fkIsingSquarePerimeterPrimalEdgeFinset n := by
    simpa [faceNorthEdge] using
      fkIsingSquareDirectionEdge_not_mem_perimeter_of_interior n
        (faceNWVertex n c) .east hNWeast
        hNWeast hNWnorth hNWwest hNWsouth
  have hnotE : (faceEastEdge n c).1 ∉
      fkIsingSquarePerimeterPrimalEdgeFinset n := by
    simpa [faceEastEdge] using
      fkIsingSquareDirectionEdge_not_mem_perimeter_of_interior n
        (faceSEVertex n c) .north hSEnorth
        hSEeast hSEnorth hSEwest hSEsouth
  have hnotS : (faceSouthEdge n c).1 ∉
      fkIsingSquarePerimeterPrimalEdgeFinset n := by
    simpa [faceSouthEdge] using
      fkIsingSquareDirectionEdge_not_mem_perimeter_of_interior n
        (faceSWVertex n c) .east hSWeast
        hSWeast hSWnorth hSWwest hSWsouth
  have hnotW : (faceWestEdge n c).1 ∉
      fkIsingSquarePerimeterPrimalEdgeFinset n := by
    simpa [faceWestEdge] using
      fkIsingSquareDirectionEdge_not_mem_perimeter_of_interior n
        (faceSWVertex n c) .north hSWnorth
        hSWeast hSWnorth hSWwest hSWsouth
  have hquad := fkIsingSquareBoundaryFullFaceFullObservable_quad
    n hn c hnotN hnotE hnotS hnotW
  unfold fkIsingSquareBoundaryCenteredRadialPatchFullObservable
  rw [hN, hE, hS, hW]
  exact hquad



theorem fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_right_of_odd
    (n J : Nat) (hn : 0 < n) (hJ0 : 0 < J) (hJ : J < 2 * n)
    (hodd : ¬ Even ((2 * n - 1) + J)) :
    IsingSquareSHolomorphicQuad
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨2 * n - 1, by omega⟩ ⟨J - 1, by omega⟩)
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨2 * n - 1, by omega⟩ ⟨J, hJ⟩)
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨2 * n - 2, by omega⟩ ⟨J, hJ⟩)
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨2 * n - 2, by omega⟩ ⟨J - 1, by omega⟩) := by
  apply
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_of_odd_faceInterior
      n (2 * n - 1) J hn (by omega) (by omega) hJ0 hJ hodd <;>
    simp [centeredRadialHalf] <;>
    have hmod := Nat.not_even_iff.mp hodd <;> omega



theorem fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_top_of_odd
    (n I : Nat) (hn : 0 < n) (hI0 : 0 < I) (hI : I < 2 * n)
    (hodd : ¬ Even (I + (2 * n - 1))) :
    IsingSquareSHolomorphicQuad
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨I, hI⟩ ⟨2 * n - 2, by omega⟩)
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨I, hI⟩ ⟨2 * n - 1, by omega⟩)
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨I - 1, by omega⟩ ⟨2 * n - 1, by omega⟩)
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
        ⟨I - 1, by omega⟩ ⟨2 * n - 2, by omega⟩) := by
  apply
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_of_odd_faceInterior
      n I (2 * n - 1) hn hI0 hI (by omega) (by omega) hodd <;>
    simp [centeredRadialHalf] <;>
    have hmod := Nat.not_even_iff.mp hodd <;> omega




theorem fkIsingSquareBoundaryCenteredRadialPatchFullObservable_cellCR
    (n i j : Nat) (hn : 0 < n)
    (hi : i + 2 < 2 * n) (hj : j + 2 < 2 * n) :
    IsingCellCRAt
      (fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension n hn)
      i j := by
  by_cases heven : Even (i + 1 + (j + 1))
  · have hquad :=
      fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad
        n (i + 1) (j + 1) hn (by omega) (by omega)
        (by omega) (by omega) heven
    unfold IsingCellCRAt
      fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension
    simp [show i < 2 * n by omega, show i + 1 < 2 * n by omega,
      show j < 2 * n by omega, show j + 1 < 2 * n by omega]
    simpa using hquad.2.2
  · have hquad :=
      fkIsingSquareBoundaryCenteredRadialPatchFullObservable_quad_of_odd
        n (i + 1) (j + 1) hn (by omega) (by omega)
        (by omega) (by omega) heven
    unfold IsingCellCRAt
      fkIsingSquareBoundaryCenteredRadialPatchFullObservableExtension
    simp [show i < 2 * n by omega, show i + 1 < 2 * n by omega,
      show j < 2 * n by omega, show j + 1 < 2 * n by omega]
    have h := hquad.2.2
    simp only [Nat.add_sub_cancel] at h
    linear_combination -h


def isingCenteredRadialGridCellPoint
    (mesh : Real) (n i j : Nat) (x y : Real) : Complex :=
  isingRadialGridCellPoint mesh i j x y - (mesh * n : Real)



def isingReflectedCenteredRadialGridCellPoint
    (mesh : Real) (n i j : Nat) (x y : Real) : Complex :=
  (starRingEnd Complex)
    (isingCenteredRadialGridCellPoint mesh n i j x y)



theorem isingReflectedCenteredRadialGridCellPoint_eq
    (mesh : Real) (n i j : Nat) (x y : Real) :
    isingReflectedCenteredRadialGridCellPoint mesh n i j x y =
      isingReflectedCenteredRadialGridPosition mesh n i j +
        (x : Complex) * ((mesh : Complex) / 2 * (1 - Complex.I)) +
        (y : Complex) * ((mesh : Complex) / 2 * (1 + Complex.I)) := by
  apply Complex.ext <;>
    simp [isingReflectedCenteredRadialGridCellPoint,
      isingCenteredRadialGridCellPoint,
      isingReflectedCenteredRadialGridPosition,
      isingCenteredRadialGridPosition, isingRadialGridCellPoint,
      isingRadialGridPosition, Complex.mul_re, Complex.mul_im] <;>
    ring



noncomputable def finiteCenteredRadialGridInterpolant
    (n : Nat) (mesh : Real)
    (value : Fin (2 * n) -> Fin (2 * n) -> Complex) : Complex -> Complex :=
  fun z => finiteRadialGridInterpolant (2 * n) mesh value
    (z + (mesh * n : Real))

theorem finiteCenteredRadialGridInterpolant_continuous
    (n : Nat) (mesh : Real)
    (value : Fin (2 * n) -> Fin (2 * n) -> Complex) :
    Continuous (finiteCenteredRadialGridInterpolant n mesh value) := by
  exact (finiteRadialGridInterpolant_continuous (2 * n) mesh value).comp
    (continuous_id.add continuous_const)

@[simp] theorem finiteCenteredRadialGridInterpolant_position
    (n : Nat) (mesh : Real) (hmesh : mesh ≠ 0)
    (value : Fin (2 * n) -> Fin (2 * n) -> Complex)
    (i j : Fin (2 * n)) :
    finiteCenteredRadialGridInterpolant n mesh value
        (isingCenteredRadialGridPosition mesh n i.1 j.1) = value i j := by
  unfold finiteCenteredRadialGridInterpolant isingCenteredRadialGridPosition
  rw [sub_add_cancel]
  exact finiteRadialGridInterpolant_position (2 * n) mesh hmesh value i j

theorem finiteCenteredRadialGridInterpolant_cellPoint
    (n : Nat) (mesh : Real) (hmesh : mesh ≠ 0)
    (value : Fin (2 * n) -> Fin (2 * n) -> Complex)
    (i j : Nat) (hi : i + 1 < 2 * n) (hj : j + 1 < 2 * n)
    (x y : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    finiteCenteredRadialGridInterpolant n mesh value
        (isingCenteredRadialGridCellPoint mesh n i j x y) =
      complexBilinearCell
        (value ⟨i, by omega⟩ ⟨j, by omega⟩)
        (value ⟨i + 1, by omega⟩ ⟨j, by omega⟩)
        (value ⟨i, by omega⟩ ⟨j + 1, by omega⟩)
        (value ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩) x y := by
  unfold finiteCenteredRadialGridInterpolant isingCenteredRadialGridCellPoint
  rw [sub_add_cancel]
  exact finiteRadialGridInterpolant_cellPoint mesh hmesh value i j hi hj
    x y hx0 hx1 hy0 hy1



noncomputable def fkIsingSquareBoundaryCenteredRadialPatchInterpolant
    (n : Nat) (hn : 0 < n) (mesh : Real) : Complex -> Complex :=
  finiteCenteredRadialGridInterpolant n mesh (fun i j =>
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn i j /
      (Real.sqrt (2 * mesh) : Complex))

theorem fkIsingSquareBoundaryCenteredRadialPatchInterpolant_continuous
    (n : Nat) (hn : 0 < n) (mesh : Real) :
    Continuous
      (fkIsingSquareBoundaryCenteredRadialPatchInterpolant n hn mesh) :=
  finiteCenteredRadialGridInterpolant_continuous n mesh _

@[simp] theorem fkIsingSquareBoundaryCenteredRadialPatchInterpolant_position
    (n : Nat) (hn : 0 < n) (mesh : Real) (hmesh : mesh ≠ 0)
    (i j : Fin (2 * n)) :
    fkIsingSquareBoundaryCenteredRadialPatchInterpolant n hn mesh
        (isingCenteredRadialGridPosition mesh n i.1 j.1) =
      fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn i j /
        (Real.sqrt (2 * mesh) : Complex) :=
  finiteCenteredRadialGridInterpolant_position n mesh hmesh _ i j



theorem fkIsingSquareBoundaryCenteredRadialPatchInterpolant_projection
    (n : Nat) (hn : 0 < n) (mesh : Real) (hmesh : 0 < mesh)
    (i j : Fin (2 * n))
    (he : (fkIsingSquareCenteredRadialPatchEdge n i j).1 ∉
      fkIsingSquarePerimeterPrimalEdgeFinset n)
    (s : FKIsingMedialSide) :
    isingProj (fkIsingSquareWiredDirectedTangent n hn
        (.dart (fkIsingSquareCenteredRadialPatchEdge n i j, s)))
      (fkIsingSquareBoundaryCenteredRadialPatchInterpolant n hn mesh
        (isingCenteredRadialGridPosition mesh n i.1 j.1)) =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain n hn).fermionicObservable
          (.dart (fkIsingSquareCenteredRadialPatchEdge n i j, s)) /
        (Real.sqrt (2 * mesh) : Complex) := by
  rw [fkIsingSquareBoundaryCenteredRadialPatchInterpolant_position
    n hn mesh hmesh.ne' i j]
  have hproj_div (u z : Complex) (r : Real) :
      isingProj u (z / (r : Complex)) = isingProj u z / (r : Complex) := by
    unfold isingProj
    simp
    ring
  rw [hproj_div]
  unfold fkIsingSquareBoundaryCenteredRadialPatchFullObservable
  exact congrArg (fun z : Complex => z / (Real.sqrt (2 * mesh) : Complex))
    (fkIsingSquareBoundaryFullMedialObservable_projection n hn _ he s)



noncomputable def fkIsingSquareBoundaryCenteredRadialPatchTwoScaleInterpolant
    (n : Nat) (hn : 0 < n)
    (gridScale normalizationScale : Real) : Complex -> Complex :=
  finiteCenteredRadialGridInterpolant n gridScale (fun i j =>
    fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn i j /
      (Real.sqrt (2 * normalizationScale) : Complex))

theorem
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleInterpolant_continuous
    (n : Nat) (hn : 0 < n)
    (gridScale normalizationScale : Real) :
    Continuous
      (fkIsingSquareBoundaryCenteredRadialPatchTwoScaleInterpolant
        n hn gridScale normalizationScale) :=
  finiteCenteredRadialGridInterpolant_continuous n gridScale _

@[simp] theorem
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleInterpolant_position
    (n : Nat) (hn : 0 < n)
    (gridScale normalizationScale : Real) (hgridScale : gridScale ≠ 0)
    (i j : Fin (2 * n)) :
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleInterpolant
        n hn gridScale normalizationScale
        (isingCenteredRadialGridPosition gridScale n i.1 j.1) =
      fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn i j /
        (Real.sqrt (2 * normalizationScale) : Complex) :=
  finiteCenteredRadialGridInterpolant_position n gridScale hgridScale _ i j



noncomputable def
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant
    (n : Nat) (hn : 0 < n)
    (gridScale normalizationScale : Real) : Complex -> Complex := fun z =>
  fkIsingSquareBoundaryCenteredRadialPatchTwoScaleInterpolant
    n hn gridScale normalizationScale ((starRingEnd Complex) z)

theorem
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_continuous
    (n : Nat) (hn : 0 < n)
    (gridScale normalizationScale : Real) :
    Continuous
      (fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant
        n hn gridScale normalizationScale) := by
  exact
    (fkIsingSquareBoundaryCenteredRadialPatchTwoScaleInterpolant_continuous
      n hn gridScale normalizationScale).comp Complex.continuous_conj

theorem
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_cellPoint
    (n i j : Nat) (hn : 0 < n)
    (gridScale normalizationScale : Real) (hgridScale : gridScale ≠ 0)
    (hi : i + 1 < 2 * n) (hj : j + 1 < 2 * n)
    (x y : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant
        n hn gridScale normalizationScale
        ((starRingEnd Complex)
          (isingCenteredRadialGridCellPoint gridScale n i j x y)) =
      complexBilinearCell
        (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
          ⟨i, by omega⟩ ⟨j, by omega⟩ /
            (Real.sqrt (2 * normalizationScale) : Complex))
        (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
          ⟨i + 1, by omega⟩ ⟨j, by omega⟩ /
            (Real.sqrt (2 * normalizationScale) : Complex))
        (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
          ⟨i, by omega⟩ ⟨j + 1, by omega⟩ /
            (Real.sqrt (2 * normalizationScale) : Complex))
        (fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn
          ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ /
            (Real.sqrt (2 * normalizationScale) : Complex)) x y := by
  unfold
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant
  have hconj : (starRingEnd Complex)
      ((starRingEnd Complex)
        (isingCenteredRadialGridCellPoint gridScale n i j x y)) =
      isingCenteredRadialGridCellPoint gridScale n i j x y := by
    apply Complex.ext <;> simp
  rw [hconj]
  exact finiteCenteredRadialGridInterpolant_cellPoint
    n gridScale hgridScale _ i j hi hj x y hx0 hx1 hy0 hy1

@[simp] theorem
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant_position
    (n : Nat) (hn : 0 < n)
    (gridScale normalizationScale : Real) (hgridScale : gridScale ≠ 0)
    (i j : Fin (2 * n)) :
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant
        n hn gridScale normalizationScale
        ((starRingEnd Complex)
          (isingCenteredRadialGridPosition gridScale n i.1 j.1)) =
      fkIsingSquareBoundaryCenteredRadialPatchFullObservable n hn i j /
        (Real.sqrt (2 * normalizationScale) : Complex) := by
  unfold
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleReflectedInterpolant
  have hconj : (starRingEnd Complex)
      ((starRingEnd Complex)
        (isingCenteredRadialGridPosition gridScale n i.1 j.1)) =
      isingCenteredRadialGridPosition gridScale n i.1 j.1 := by
    apply Complex.ext <;> simp
  rw [hconj]
  exact
    fkIsingSquareBoundaryCenteredRadialPatchTwoScaleInterpolant_position
      n hn gridScale normalizationScale hgridScale i j

end

end StatMech.Universality
