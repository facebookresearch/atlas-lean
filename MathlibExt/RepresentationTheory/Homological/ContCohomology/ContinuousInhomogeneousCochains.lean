/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import Mathlib.CategoryTheory.Action.Continuous
public import MathlibExt.RepresentationTheory.Homological.ContCohomology.InvariantHomogeneousComplex

/-!
# Continuous homogeneous and inhomogeneous cochain spaces

Let k be a ring with a topology, G a profinite group and X a discrete
topological k-module with jointly continuous G-action.
A homogeneous q-cochain is a continuous equivariant function
F : G^(q+1) → X. Its inhomogeneous coordinates are continuous functions
h : G^q → X.

For g=(g₀,…,g_(q-1)), define prefix vertices
v₀=1 and v_(i+1)=v_i g_i. Inhomogenization is F ↦ (g ↦ F(v(g))).
For t=(t₀,…,t_q), put d_i(t)=t_i⁻¹t_(i+1).
The inverse sends h to t ↦ t₀ • h(d(t)).
These are continuous k-linear equivalences in each nonnegative degree.
At q=0 the cochain space is X, by evaluation at the identity vertex.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
universe u v w
namespace ContinuousCohomology
variable {k : Type u} [Ring k] [TopologicalSpace k]
variable (G : ProfiniteGrp.{v})

private theorem partialProd_continuous (q : ℕ) (i : Fin (q + 1)) :
    Continuous (fun g : Fin q → G => Fin.partialProd g i) := by
  induction i using Fin.induction with
  | zero => simpa only [Fin.partialProd_zero] using
      (continuous_const : Continuous (fun _ : Fin q → G => (1 : G)))
  | succ i hi =>
      have h := hi.mul (continuous_apply i)
      change Continuous (fun g : Fin q → G => Fin.partialProd g i.castSucc * g i) at h
      simpa only [Fin.partialProd_succ] using h

/-- For a profinite group G and q ∈ ℕ, the continuous prefix-vertex
map G^q → G^(q+1) sends g to v₀=1,
v_(i+1)=v_i g_i. Products retain the order of the group coordinates. -/
def inhomogeneousVerticesCM (q : ℕ) : C(Fin q → G, Fin (q + 1) → G) :=
  ⟨Fin.partialProd, continuous_pi fun i => by exact partialProd_continuous G q i⟩

/-- For a profinite group G and q ∈ ℕ, the continuous difference
map G^(q+1) → G^q sends t to
d_i(t)=t_i⁻¹t_(i+1). The inverse is on the earlier coordinate. -/
def homogeneousDifferencesCM (q : ℕ) : C(Fin (q + 1) → G, Fin q → G) :=
  ⟨fun t i => (t i.castSucc)⁻¹ * t i.succ,
    continuous_pi fun i => (continuous_apply i.castSucc).inv.mul (continuous_apply i.succ)⟩

variable (A : DiscreteContAction (TopModuleCat.{max v w} k) G)
/-- Let k be a ring with a topology, G a profinite group and A a
discrete topological k-module with jointly continuous G-action.
Write X for this coefficient as a topological k-representation.
This is X with its given coefficient carrier, scalar topology
and G-action, viewed in the topological representation category. -/
abbrev inhomogeneousOriginalTopRep : TopRep.{max v w, u, v} k G :=
  (TopRep.fromActionTopModFunc (k := k) (G := G)).obj A.obj.obj
local notation "X" => inhomogeneousOriginalTopRep G A

private theorem original_action_continuous :
    Continuous (fun p : G × X => (inhomogeneousOriginalTopRep G A).ρ p.1 p.2) := by
  have h := (Action.isContinuous_def A.obj.obj).mp A.obj.property
  change Continuous (fun p : G × X => (inhomogeneousOriginalTopRep G A).ρ p.1 p.2) at h
  exact h

/-- Let k be a ring with a topology, G a profinite group and A a
discrete topological k-module with jointly continuous G-action.
Write X for this coefficient as a topological k-representation.
For q ∈ ℕ, the continuous k-linear map from homogeneous to
inhomogeneous cochains sends F to g ↦ F(v(g)), where
v₀=1 and v_(i+1)=v_i g_i. -/
def inhomogeneousPhi (q : ℕ) :
    flatHomogeneousCochains X q →L[k] C(Fin q → G, X) where
  toFun f := f.val.comp (inhomogeneousVerticesCM G q)
  map_add' _ _ := by ext t; rfl
  map_smul' _ _ := by ext t; rfl
  cont := (ContinuousMap.continuous_precomp (inhomogeneousVerticesCM G q)).comp
    continuous_subtype_val

/-- Let k be a ring with a topology, G a profinite group and A a
discrete topological k-module with jointly continuous G-action.
Write X for this coefficient as a topological k-representation.
For q ∈ ℕ, the continuous k-linear homogenization map sends
h : G^q → X to F(t)=t₀ • h(t₀⁻¹t₁,…,t_(q-1)⁻¹t_q).
The resulting function is homogeneous-equivariant. -/
def inhomogeneousPsi (q : ℕ) :
    C(Fin q → G, X) →L[k] flatHomogeneousCochains X q where
  toFun h := ⟨⟨fun t => (inhomogeneousOriginalTopRep G A).ρ (t 0)
    (h (homogeneousDifferencesCM G q t)),
    by exact (original_action_continuous G A).comp ((continuous_apply 0).prodMk
      (h.continuous.comp (homogeneousDifferencesCM G q).continuous))⟩, by
    intro g t
    have hd : homogeneousDifferencesCM G q (fun i => g * t i) =
        homogeneousDifferencesCM G q t := by
      funext i
      change (g * t i.castSucc)⁻¹ * (g * t i.succ) = (t i.castSucc)⁻¹ * t i.succ
      simp [mul_assoc]
    change (inhomogeneousOriginalTopRep G A).ρ (g * t 0)
      (h (homogeneousDifferencesCM G q (fun i => g * t i))) =
      (inhomogeneousOriginalTopRep G A).ρ g
        ((inhomogeneousOriginalTopRep G A).ρ (t 0) (h (homogeneousDifferencesCM G q t)))
    rw [hd, map_mul]
    rfl⟩
  map_add' _ _ := by
    apply Subtype.ext
    ext t
    exact map_add ((inhomogeneousOriginalTopRep G A).ρ (t 0)) _ _
  map_smul' _ _ := by
    apply Subtype.ext
    ext t
    exact map_smul ((inhomogeneousOriginalTopRep G A).ρ (t 0)) _ _
  cont := by
    apply Continuous.subtype_mk
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (original_action_continuous G A).comp
      (((continuous_apply 0).comp continuous_snd).prodMk
        (continuous_fst.eval ((homogeneousDifferencesCM G q).continuous.comp continuous_snd)))

/-- Let k be a ring with a topology, G a profinite group and A a
discrete topological k-module with jointly continuous G-action.
Write X for this coefficient as a topological k-representation.
The maps F ↦ F(v(g)) and h ↦ (t ↦ t₀ • h(d(t))) are inverse
continuous k-linear equivalences between homogeneous and inhomogeneous
degree q cochains, for all q ∈ ℕ. -/
def inhomogeneousContinuousEquiv (q : ℕ) :
    flatHomogeneousCochains X q ≃L[k] C(Fin q → G, X) :=
  ContinuousLinearEquiv.equivOfInverse (inhomogeneousPhi G A q) (inhomogeneousPsi G A q)
    (by
      intro f
      apply Subtype.ext
      ext t
      change (inhomogeneousOriginalTopRep G A).ρ (t 0)
        (f.val (Fin.partialProd (homogeneousDifferencesCM G q t))) = f.val t
      have ht : (fun i => t 0 * Fin.partialProd (homogeneousDifferencesCM G q t) i) = t := by
        have h := Fin.partialProd_left_inv t
        change (fun i => t 0 * Fin.partialProd (fun j => (t j.castSucc)⁻¹ * t j.succ) i) = t at h
        exact h
      exact (f.property (t 0) _).symm.trans (congrArg f.val ht))
    (by
      intro h
      ext g
      have hd : homogeneousDifferencesCM G q (Fin.partialProd g) = g := by
        funext i
        exact Fin.partialProd_right_inv g i
      change (inhomogeneousOriginalTopRep G A).ρ (Fin.partialProd g 0)
        (h (homogeneousDifferencesCM G q (Fin.partialProd g))) = h g
      rw [Fin.partialProd_zero, hd]
      simp)

/-- Let k be a ring with a topology, G a profinite group and A a
discrete topological k-module with jointly continuous G-action.
Write X for this coefficient as a topological k-representation.
The forward degree q equivalence has value Φ(F)(g)=F(v(g)),
with the ordered prefix vertices v₀=1, v_(i+1)=v_i g_i. -/
theorem inhomogeneousContinuousEquiv_apply (q : ℕ)
    (f : flatHomogeneousCochains X q) (g : Fin q → G) :
    inhomogeneousContinuousEquiv G A q f g = f.val (Fin.partialProd g) := rfl

/-- Let k be a ring with a topology, G a profinite group and A a
discrete topological k-module with jointly continuous G-action.
Write X for this coefficient as a topological k-representation.
The inverse degree q equivalence has value
Ψ(h)(t)=t₀ • h(d(t)), with d_i(t)=t_i⁻¹t_(i+1). -/
theorem inhomogeneousContinuousEquiv_symm_apply (q : ℕ)
    (h : C(Fin q → G, X)) (t : Fin (q + 1) → G) :
    ((inhomogeneousContinuousEquiv G A q).symm h).val t =
      (inhomogeneousOriginalTopRep G A).ρ (t 0) (h (homogeneousDifferencesCM G q t)) := rfl

/-- Let k be a ring with a topology, G a profinite group and A a
discrete topological k-module with jointly continuous G-action.
Write X for this coefficient as a topological k-representation.
The degree-zero homogeneous cochain space is continuously
k-linearly equivalent to X. The equivalence evaluates the single
homogeneous group coordinate at 1. -/
def inhomogeneousZeroEquiv : flatHomogeneousCochains X 0 ≃L[k] X :=
  (inhomogeneousContinuousEquiv G A 0).trans
    (resolutionFinContinuousLinearEquiv X 0).symm

/-- Let k be a ring with a topology, G a profinite group and A a
discrete topological k-module with jointly continuous G-action.
Write X for this coefficient as a topological k-representation.
For the unique empty tuple g ∈ G^0, degree-zero
inhomogenization satisfies Φ(F)(g)=F(1). -/
theorem inhomogeneousContinuousEquiv_zero (f : flatHomogeneousCochains X 0)
    (g : Fin 0 → G) :
    inhomogeneousContinuousEquiv G A 0 f g = f.val (fun _ => 1) := by
  rw [inhomogeneousContinuousEquiv_apply]
  congr 1
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  exact Fin.partialProd_zero g
end ContinuousCohomology
