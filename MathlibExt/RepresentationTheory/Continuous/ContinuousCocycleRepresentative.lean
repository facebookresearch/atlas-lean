/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.RepresentationTheory.Continuous.ContinuousCocycleClass
public import MathlibExt.RepresentationTheory.Continuous.ContinuousHomology
public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Mathlib.Topology.Separation.Connected
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Tactic.Group

/-!
# Recovering continuous inhomogeneous one-cocycles

A homogeneous degree-one continuous cycle f determines c(g) = f(1,g). Diagonal equivariance
reconstructs f(x,y) = ρ(x)c(x⁻¹y), and the differential formula d¹f(x,y,z) = f(y,z) − f(x,z) +
f(x,y) gives c(gh) = ρ(g)c(h) + c(g).

Every continuous H¹ class has a homogeneous cycle representative. When the coefficient module
is discrete and the group is compact and totally disconnected, a continuous one-cocycle
vanishes on some open normal subgroup, and that subgroup fixes every value of the cocycle.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory TopRep ContRepresentation

universe u v w

namespace ContinuousCohomology

variable {k : Type u} {G : Type v} [Ring k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ContinuousAdd k] [ContinuousSMul k k]

omit [ContinuousAdd k] [ContinuousSMul k k] in
/-- Homogeneous representatives of continuous degree-one classes.

For a topological representation X over k, every element of continuous H¹(G,X) is the image of
a homogeneous continuous one-cycle under the homology projection. -/
theorem degreeOneπ_surjective
    (X : TopRep.{max v u w} k G) :
    Function.Surjective (π.{u, v, max u w} X 1) := by
  exact π_surjective_succ X 0

/-- The inhomogeneous function of a homogeneous one-cycle.

Include z into the homogeneous degree-one cochains and evaluate at (1,g). This defines c(g) =
f(1,g) for the included cochain f. -/
def inhomogeneousOneCocycle
    (X : TopRep.{max v u w} k G)
    (z : cocycles.{u, v, max u w} X 1) (g : G) : X :=
  ((TopRep.homogeneousCochains.{u, v, max u w} X).iCycles 1 z).val 1 g

omit [ContinuousAdd k] [ContinuousSMul k k] in
/-- Continuity of the inhomogeneous evaluation.

For a homogeneous continuous one-cycle z, the function g ↦ f(1,g), with f its included
cochain, is continuous. -/
theorem inhomogeneousOneCocycle_continuous
    (X : TopRep.{max v u w} k G)
    (z : cocycles.{u, v, max u w} X 1) :
    Continuous (inhomogeneousOneCocycle X z) :=
  (((TopRep.homogeneousCochains.{u, v, max u w} X).iCycles 1 z).val 1).continuous

omit [ContinuousAdd k] [ContinuousSMul k k] in
/-- Reconstruction by diagonal equivariance.

For the inhomogeneous function c(g) = f(1,g) extracted from a homogeneous cycle, every value
of f satisfies f(x,y) = ρ(x)c(x⁻¹y). -/
theorem inhomogeneousOneCocycle_homogeneous_value
    (X : TopRep.{max v u w} k G)
    (z : cocycles.{u, v, max u w} X 1) (x y : G) :
    X.ρ x (inhomogeneousOneCocycle X z (x⁻¹ * y)) =
      ((TopRep.homogeneousCochains.{u, v, max u w} X).iCycles 1 z).val x y := by
  let K := TopRep.homogeneousCochains.{u, v, max u w} X
  let f : K.X 1 := K.iCycles 1 z
  have hinv := (mem_invariants f.val).mp f.property x
  have hvalue := congrArg (fun q : C(G, C(G, X)) => q x y) hinv
  change X.ρ x (f.val (x⁻¹ * x) (x⁻¹ * y)) = f.val x y at hvalue
  simpa only [inv_mul_cancel, inhomogeneousOneCocycle, f, K] using hvalue

omit [ContinuousAdd k] [ContinuousSMul k k] in
/-- Homogenization recovers the included cycle cochain.

If the homogenization of the function c extracted from z is jointly continuous, then
homOneCochain X c equals the homogeneous cochain obtained by including z into C¹. -/
theorem homOneCochain_inhomogeneousOneCocycle
    (X : TopRep.{max v u w} k G)
    (z : cocycles.{u, v, max u w} X 1)
    (hcont : Continuous (fun p : G × G =>
      X.ρ p.1 (inhomogeneousOneCocycle X z (p.1⁻¹ * p.2)))) :
    homOneCochain.{u, v, max u w} X
      (inhomogeneousOneCocycle X z) hcont =
      (TopRep.homogeneousCochains.{u, v, max u w} X).iCycles 1 z := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro y
  rw [homOneCochain_val_apply.{u, v, max u w}]
  exact inhomogeneousOneCocycle_homogeneous_value X z x y

omit [ContinuousAdd k] [ContinuousSMul k k] in
/-- The alternating homogeneous degree-one differential.

For an arbitrary homogeneous one-cochain f, its differential has value d¹f(x,y,z) = f(y,z) −
f(x,z) + f(x,y). -/
theorem homogeneousOneCochain_d_apply
    (X : TopRep.{max v u w} k G)
    (f : (TopRep.homogeneousCochains.{u, v, max u w} X).X 1)
    (x y z : G) :
    (((TopRep.homogeneousCochains.{u, v, max u w} X).d 1 2).hom f).val
        x y z = f.val y z - f.val x z + f.val x y := by
  let K := TopRep.homogeneousCochains.{u, v, max u w} X
  rw [TopRep.homogeneousCochains.d_apply]
  simp only [TopRep.hom_d_succ, TopRep.hom_ofHom, TopRep.d_zero,
    ContIntertwiningMap.sub_apply, ContRepresentation.coind₁ι_toFun,
    ContRepresentation.coind₁Map_toFun, ContinuousMap.const_apply,
    ContinuousMap.comp_apply, ContinuousMap.sub_apply]
  let hF : C(G, X) := f.val x
  have hRem : (X.ρ.coind₁ι (hF y)) z = hF y := by
    simp only [ContRepresentation.coind₁ι_toFun, ContinuousMap.const_apply]
  have hInnerDirect :
      ((((TopRep.resolutionX.{u, v, max u w} X 0).ρ.coind₁.coind₁ι -
      ContRepresentation.coind₁Map X.ρ.coind₁ι) hF) y) z =
      hF z - hF y := by
    simp only [ContIntertwiningMap.sub_apply,
      ContRepresentation.coind₁ι_toFun,
      ContRepresentation.coind₁Map_toFun, ContinuousMap.const_apply,
      ContinuousMap.comp_apply, ContinuousMap.sub_apply]
    change hF z - (X.ρ.coind₁ι (hF y)) z = hF z - hF y
    rw [hRem]
  change f.val y z -
    ((((TopRep.resolutionX.{u, v, max u w} X 0).ρ.coind₁.coind₁ι -
      ContRepresentation.coind₁Map X.ρ.coind₁ι) hF) y) z =
    f.val y z - f.val x z + f.val x y
  rw [hInnerDirect]
  abel

private theorem eq_add_of_sub_add_eq_zero {A : Type*} [AddCommGroup A]
    {a b c : A} (h : a - b + c = 0) : b = a + c := by
  apply sub_eq_zero.mp
  calc
    b - (a + c) = -(a - b + c) := by abel
    _ = 0 := by rw [h, neg_zero]

private theorem eq_zero_of_eq_add_self {A : Type*} [AddCommGroup A]
    {a : A} (h : a = a + a) : a = 0 := by
  have h' : 0 + a = a + a := by simpa only [zero_add] using h
  exact (add_right_cancel h').symm

omit [ContinuousAdd k] [ContinuousSMul k k] in
/-- The cocycle equation of the extracted function.

For a homogeneous continuous one-cycle z, its extracted function c satisfies c(gh) = ρ(g)c(h)
+ c(g) for all g,h ∈ G. -/
theorem inhomogeneousOneCocycle_cocycle
    (X : TopRep.{max v u w} k G)
    (z : cocycles.{u, v, max u w} X 1) (g h : G) :
    inhomogeneousOneCocycle X z (g * h) =
      X.ρ g (inhomogeneousOneCocycle X z h) +
        inhomogeneousOneCocycle X z g := by
  let K := TopRep.homogeneousCochains.{u, v, max u w} X
  let f : K.X 1 := K.iCycles 1 z
  have hdf : (K.d 1 2).hom f = 0 := by
    have hcomp := ConcreteCategory.congr_hom (K.iCycles_d 1 2) z
    change (K.d 1 2).hom (K.iCycles 1 z) = 0 at hcomp
    exact hcomp
  have hdiff : f.val g (g * h) - f.val 1 (g * h) + f.val 1 g = 0 := by
    have hvalue := congrArg (fun t : K.X 2 => t.val 1 g (g * h)) hdf
    rw [homogeneousOneCochain_d_apply] at hvalue
    exact hvalue
  have hfg : f.val g (g * h) =
      X.ρ g (inhomogeneousOneCocycle X z h) := by
    have hvalue :=
      (inhomogeneousOneCocycle_homogeneous_value X z g (g * h)).symm
    simpa only [inv_mul_cancel_left, f, K] using hvalue
  change f.val g (g * h) - inhomogeneousOneCocycle X z (g * h) +
    inhomogeneousOneCocycle X z g = 0 at hdiff
  rw [hfg] at hdiff
  exact eq_add_of_sub_add_eq_zero hdiff

/-- The included value of the rank-one cycle map at one.

For a cocycle c with jointly continuous homogenization, applying its cycle map to the lifted
scalar 1 and then including into C¹ gives homOneCochain X c. -/
theorem oneCocycleMor_apply_one_iCycles
    (X : TopRep.{max v u w} k G) (c : G → X)
    (hcocycle : ∀ g h : G, c (g * h) = X.ρ g (c h) + c g)
    (hcont : Continuous (fun p : G × G =>
      X.ρ p.1 (c (p.1⁻¹ * p.2)))) :
    (TopRep.homogeneousCochains.{u, v, max u w} X).iCycles 1
        (oneCocycleMor.{u, v, w} X c hcocycle hcont
          (ULift.up (1 : k))) =
      homOneCochain.{u, v, max u w} X c hcont := by
  unfold oneCocycleMor
  rw [← ConcreteCategory.comp_apply,
    HomologicalComplex.liftCycles_i]
  simp only [TopModuleCat.hom_ofHom, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, uliftDown]
  change (1 : k) • _ = _
  rw [one_smul]

/-- Recovery of a cycle from its inhomogeneous values.

Let z be a homogeneous continuous one-cycle. If c(g) equals the inhomogeneous function of z
for every g, and c has the stated cocycle and joint-continuity properties, then its rank-one
cycle map sends the lifted scalar 1 to z. -/
theorem oneCocycleMor_apply_one_eq_of_eq_inhomogeneousOneCocycle
    (X : TopRep.{max v u w} k G)
    (z : cocycles.{u, v, max u w} X 1) (c : G → X)
    (hcocycle : ∀ g h : G, c (g * h) = X.ρ g (c h) + c g)
    (hcont : Continuous (fun p : G × G =>
      X.ρ p.1 (c (p.1⁻¹ * p.2))))
    (hc : ∀ g : G, c g = inhomogeneousOneCocycle X z g) :
    oneCocycleMor.{u, v, w} X c hcocycle hcont
        (ULift.up (1 : k)) = z := by
  let K := TopRep.homogeneousCochains.{u, v, max u w} X
  apply (ModuleCat.mono_iff_injective
    ((forget₂ (TopModuleCat k) (ModuleCat k)).map (K.iCycles 1))).mp
      inferInstance
  change (K.iCycles 1).hom
      (oneCocycleMor.{u, v, w} X c hcocycle hcont
        (ULift.up (1 : k))) = (K.iCycles 1).hom z
  rw [oneCocycleMor_apply_one_iCycles]
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro y
  rw [homOneCochain_val_apply, hc]
  exact inhomogeneousOneCocycle_homogeneous_value X z x y

omit [ContinuousAdd k] [ContinuousSMul k k] in
/-- A normal subgroup annihilating a continuous discrete cocycle.

For a compact totally disconnected topological group G and a discrete topological
representation X, every continuous one-cocycle c vanishes on an open normal subgroup H. Every
h ∈ H also satisfies ρ(h)c(g) = c(g) for all g ∈ G. -/
theorem exists_openNormalSubgroup_le_cocycle_zero_and_fixed
    (X : TopRep.{max v u w} k G) [DiscreteTopology X]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (c : G → X)
    (hcocycle : ∀ g h : G, c (g * h) = X.ρ g (c h) + c g)
    (hcontinuous : Continuous c) :
    ∃ H : OpenNormalSubgroup G,
      (∀ h : G, h ∈ H → c h = 0) ∧
        ∀ h : G, h ∈ H → ∀ g : G, X.ρ h (c g) = c g := by
  have hcOne : c 1 = 0 := by
    have h := hcocycle 1 1
    simp only [one_mul, map_one, one_apply_eq_self] at h
    exact eq_zero_of_eq_add_self h
  let U : Set G := c ⁻¹' {0}
  have hUOpen : IsOpen U :=
    hcontinuous.isOpen_preimage {0} (isOpen_discrete {0})
  have hOneU : 1 ∈ U := by
    change c 1 = 0
    exact hcOne
  obtain ⟨H, hHU⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      hUOpen hOneU
  have hzero : ∀ h : G, h ∈ H → c h = 0 := by
    intro h hh
    exact Set.mem_singleton_iff.mp (hHU hh)
  refine ⟨H, hzero, ?_⟩
  intro h hh g
  let q := g⁻¹ * h * g
  have hq : q ∈ H := by
    exact Subgroup.Normal.conj_mem' inferInstance h hh g
  have hhg : h * g = g * q := by
    dsimp only [q]
    group
  calc
    X.ρ h (c g) = X.ρ h (c g) + c h := by rw [hzero h hh, add_zero]
    _ = c (h * g) := (hcocycle h g).symm
    _ = c (g * q) := by rw [hhg]
    _ = X.ρ g (c q) + c g := hcocycle g q
    _ = c g := by rw [hzero q hq, map_zero, zero_add]

end ContinuousCohomology
