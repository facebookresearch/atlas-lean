/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingCoordinateReflectionGeometry

namespace StatMech.FrontierA

open StatMech Ising Lattice StatMech.FrontierB

variable {d : Nat}

section

variable (K : Finset (Site d)) (i : Fin d) (m : Int)

def isingCoordinateDomainPlane (x : freeDomainVertices K) : Prop :=
  isingCoordinatePlane i m x.1

def isingCoordinateDomainLower (x : freeDomainVertices K) : Prop :=
  isingCoordinateLower i m x.1

instance (x : freeDomainVertices K) :
    Decidable (isingCoordinateDomainPlane K i m x) := by
  unfold isingCoordinateDomainPlane isingCoordinatePlane
  infer_instance

instance (x : freeDomainVertices K) :
    Decidable (isingCoordinateDomainLower K i m x) := by
  unfold isingCoordinateDomainLower isingCoordinateLower
  infer_instance

abbrev IsingCoordinateDomainPlane :=
  {x : freeDomainVertices K // isingCoordinateDomainPlane K i m x}

abbrev IsingCoordinateDomainLower :=
  {x : freeDomainVertices K // isingCoordinateDomainLower K i m x}

variable (hK : ∀ x : Site d,
  x ∈ K ↔ isingCoordinateReflect i m x ∈ K)

def isingCoordinateDomainReflectEquiv :
    freeDomainVertices K ≃ freeDomainVertices K where
  toFun x := ⟨isingCoordinateReflect i m x.1, (hK x.1).1 x.2⟩
  invFun x := ⟨isingCoordinateReflect i m x.1, (hK x.1).1 x.2⟩
  left_inv x := by
    apply Subtype.ext
    exact isingCoordinateReflect_involutive i m x.1
  right_inv x := by
    apply Subtype.ext
    exact isingCoordinateReflect_involutive i m x.1

@[simp] theorem isingCoordinateDomainReflectEquiv_val
    (x : freeDomainVertices K) :
    (isingCoordinateDomainReflectEquiv K i m hK x).1 =
      isingCoordinateReflect i m x.1 := rfl

theorem isingCoordinateDomainReflectEquiv_adj
    (x y : freeDomainVertices K) :
    (freeDomainGraph K).Adj x y ↔
      (freeDomainGraph K).Adj
        (isingCoordinateDomainReflectEquiv K i m hK x)
        (isingCoordinateDomainReflectEquiv K i m hK y) :=
  hypercubicLattice_adj_coordinateReflect i m x.1 y.1

theorem isingCoordinateDomainReflect_fixed
    {x : freeDomainVertices K}
    (hx : isingCoordinateDomainPlane K i m x) :
    isingCoordinateDomainReflectEquiv K i m hK x = x := by
  apply Subtype.ext
  exact isingCoordinateReflect_fixed i m x.1 hx

theorem isingCoordinateDomainReflect_lower_of_upper
    {x : freeDomainVertices K}
    (hp : ¬ isingCoordinateDomainPlane K i m x)
    (hl : ¬ isingCoordinateDomainLower K i m x) :
    isingCoordinateDomainLower K i m
      (isingCoordinateDomainReflectEquiv K i m hK x) :=
  isingCoordinateReflect_lower_of_upper i m x.1 hp hl

theorem isingCoordinateDomainReflect_not_plane
    {x : freeDomainVertices K}
    (hp : ¬ isingCoordinateDomainPlane K i m x) :
    ¬ isingCoordinateDomainPlane K i m
      (isingCoordinateDomainReflectEquiv K i m hK x) :=
  isingCoordinateReflect_not_plane i m x.1 hp

theorem isingCoordinateDomainReflect_not_lower_of_lower
    {x : freeDomainVertices K}
    (hl : isingCoordinateDomainLower K i m x) :
    ¬ isingCoordinateDomainLower K i m
      (isingCoordinateDomainReflectEquiv K i m hK x) :=
  isingCoordinateReflect_not_lower_of_lower i m x.1 hl

def isingCoordinateDomainGlue
    (boundary : ConfigSpace (IsingCoordinateDomainPlane K i m))
    (lower upper : ConfigSpace (IsingCoordinateDomainLower K i m)) :
    ConfigSpace (freeDomainVertices K) :=
  fun x => if hp : isingCoordinateDomainPlane K i m x then
      boundary ⟨x, hp⟩
    else if hl : isingCoordinateDomainLower K i m x then
      lower ⟨x, hl⟩
    else upper ⟨isingCoordinateDomainReflectEquiv K i m hK x,
      isingCoordinateDomainReflect_lower_of_upper K i m hK hp hl⟩

def isingCoordinateDomainSplit
    (sigma : ConfigSpace (freeDomainVertices K)) :
    ConfigSpace (IsingCoordinateDomainPlane K i m) ×
      (ConfigSpace (IsingCoordinateDomainLower K i m) ×
        ConfigSpace (IsingCoordinateDomainLower K i m)) :=
  (fun x => sigma x.1,
    (fun x => sigma x.1,
      fun x => sigma (isingCoordinateDomainReflectEquiv K i m hK x.1)))

@[simp] theorem isingCoordinateDomainSplit_glue
    (boundary : ConfigSpace (IsingCoordinateDomainPlane K i m))
    (lower upper : ConfigSpace (IsingCoordinateDomainLower K i m)) :
    isingCoordinateDomainSplit K i m hK
        (isingCoordinateDomainGlue K i m hK boundary lower upper) =
      (boundary, (lower, upper)) := by
  apply Prod.ext
  · funext x
    simp [isingCoordinateDomainSplit, isingCoordinateDomainGlue, x.2]
  · apply Prod.ext
    · funext x
      have hp : ¬ isingCoordinateDomainPlane K i m x.1 := by
        intro hplane
        have hl : 2 * x.1.1 i < m := x.2
        have heq : 2 * x.1.1 i = m := hplane
        omega
      simp [isingCoordinateDomainSplit, isingCoordinateDomainGlue, hp, x.2]
    · funext x
      have hp : ¬ isingCoordinateDomainPlane K i m x.1 := by
        intro hplane
        have hl : 2 * x.1.1 i < m := x.2
        have heq : 2 * x.1.1 i = m := hplane
        omega
      have hpR := isingCoordinateDomainReflect_not_plane K i m hK hp
      have hlR := isingCoordinateDomainReflect_not_lower_of_lower
        K i m hK x.2
      have hRR : isingCoordinateDomainReflectEquiv K i m hK
          (isingCoordinateDomainReflectEquiv K i m hK x.1) = x.1 :=
        (isingCoordinateDomainReflectEquiv K i m hK).left_inv x.1
      simp [isingCoordinateDomainSplit, isingCoordinateDomainGlue,
        hpR, hlR, hRR]

@[simp] theorem isingCoordinateDomainGlue_split
    (sigma : ConfigSpace (freeDomainVertices K)) :
    isingCoordinateDomainGlue K i m hK
        (isingCoordinateDomainSplit K i m hK sigma).1
        (isingCoordinateDomainSplit K i m hK sigma).2.1
        (isingCoordinateDomainSplit K i m hK sigma).2.2 = sigma := by
  funext x
  by_cases hp : isingCoordinateDomainPlane K i m x
  · simp [isingCoordinateDomainGlue, isingCoordinateDomainSplit, hp]
  · by_cases hl : isingCoordinateDomainLower K i m x
    · simp [isingCoordinateDomainGlue, isingCoordinateDomainSplit, hp, hl]
    · have hRR : isingCoordinateDomainReflectEquiv K i m hK
          (isingCoordinateDomainReflectEquiv K i m hK x) = x :=
        (isingCoordinateDomainReflectEquiv K i m hK).left_inv x
      simp [isingCoordinateDomainGlue, isingCoordinateDomainSplit, hp, hl, hRR]

def isingCoordinateDomainSplitEquiv :
    (ConfigSpace (IsingCoordinateDomainPlane K i m) ×
      (ConfigSpace (IsingCoordinateDomainLower K i m) ×
        ConfigSpace (IsingCoordinateDomainLower K i m))) ≃
      ConfigSpace (freeDomainVertices K) where
  toFun p := isingCoordinateDomainGlue K i m hK p.1 p.2.1 p.2.2
  invFun := isingCoordinateDomainSplit K i m hK
  left_inv p := by rcases p with ⟨b, l, u⟩; simp
  right_inv := isingCoordinateDomainGlue_split K i m hK

theorem isingCoordinateDomainGlue_reflect
    (boundary : ConfigSpace (IsingCoordinateDomainPlane K i m))
    (lower upper : ConfigSpace (IsingCoordinateDomainLower K i m)) :
    isingCfgEquiv (isingCoordinateDomainReflectEquiv K i m hK)
        (isingCoordinateDomainGlue K i m hK boundary lower upper) =
      isingCoordinateDomainGlue K i m hK boundary upper lower := by
  funext x
  by_cases hp : isingCoordinateDomainPlane K i m x
  · have hfixed := isingCoordinateDomainReflect_fixed K i m hK hp
    simp [isingCfgEquiv, isingCoordinateDomainGlue, hp, hfixed]
  · by_cases hl : isingCoordinateDomainLower K i m x
    · have hpR := isingCoordinateDomainReflect_not_plane K i m hK hp
      have hlR := isingCoordinateDomainReflect_not_lower_of_lower
        K i m hK hl
      have hRR : isingCoordinateDomainReflectEquiv K i m hK
          (isingCoordinateDomainReflectEquiv K i m hK x) = x :=
        (isingCoordinateDomainReflectEquiv K i m hK).left_inv x
      simp [isingCfgEquiv, isingCoordinateDomainGlue,
        hp, hl, hpR, hlR, hRR]
    · have hlR := isingCoordinateDomainReflect_lower_of_upper
        K i m hK hp hl
      have hpR := isingCoordinateDomainReflect_not_plane K i m hK hp
      simp [isingCfgEquiv, isingCoordinateDomainGlue, hp, hl, hpR, hlR]

end

end StatMech.FrontierA
