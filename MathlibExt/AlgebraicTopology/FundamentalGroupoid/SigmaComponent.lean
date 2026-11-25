/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.FundamentalGroupoid.PathTransportNaturality
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Constructions
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Original fundamental groups of sigma components

Each original sigma inclusion has clopen range. An actual path starting in
that range stays there, by preconnectedness of its unit-interval domain.
The continuous decoder uses the transported original value in that same
component and the original selected point on all other components.

These maps give inverse maps of the original endpoint-fixed path classes,
and hence full faithfulness of the induced component groupoid functor.
The original based End map is bijective and yields a multiplicative
equivalence with the literal sigma image basepoint. Index and carrier
universes are independent; no connectedness of the sigma family is assumed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Topology
open scoped unitInterval

universe u v

namespace FundamentalGroupoid.SigmaComponent

variable {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]

/-- The actual inclusion of the original indexed space into its original sigma. -/
def inclusion (i : ι) : C(X i, Σ j, X j) where
  toFun := Sigma.mk i
  continuous_toFun := by exact continuous_sigmaMk

/-- The inclusion retains both the original index and the original point. -/
theorem inclusion_apply (i : ι) (x : X i) : inclusion X i x = Sigma.mk i x :=
  rfl

/-- Decode the selected component, using the original selected point on every other component. -/
def decoder (i : ι) (x₀ : X i) : C((Σ j, X j), X i) := by
  classical
  exact
    { toFun := fun z => if h : z.1 = i then Eq.mp (congrArg X h) z.2 else x₀
      continuous_toFun := by
        apply continuous_sigma
        intro j
        by_cases hj : j = i
        · subst j
          have hf : (fun x : X i => if h : i = i then Eq.mp (congrArg X h) x else x₀) =
              (fun x : X i => x) := by
            funext x
            rw [dite_eq_left (rfl : i = i)]
            rfl
          change Continuous (fun x : X i => if h : i = i then Eq.mp (congrArg X h) x else x₀)
          rw [hf]
          exact continuous_id
        · simpa only [dite_eq_right hj] using
            (continuous_const : Continuous (fun _ : X j => x₀)) }

/-- The original point is recovered on the selected component, regardless of the default point. -/
@[simp]
theorem decoder_mk (i : ι) (x₀ x : X i) : decoder X i x₀ (Sigma.mk i x) = x := by
  classical
  change (if h : i = i then Eq.mp (congrArg X h) x else x₀) = x
  rw [dite_eq_left (rfl : i = i)]
  rfl

/-- Other components are sent to the same original selected default point. -/
theorem decoder_mk_ne (i : ι) (x₀ : X i) {j : ι} (hj : j ≠ i) (x : X j) :
    decoder X i x₀ (Sigma.mk j x) = x₀ := by
  classical
  change (if h : j = i then Eq.mp (congrArg X h) x else x₀) = x₀
  exact dite_eq_right hj

/-- The actual decoder after the actual inclusion is the identity on the original component. -/
theorem decoder_inclusion (i : ι) (x₀ x : X i) : decoder X i x₀ (inclusion X i x) = x :=
  decoder_mk X i x₀ x

/-- Inclusion after decoding fixes every actual point in the selected sigma range. -/
theorem inclusion_decoder_of_mem_range (i : ι) (x₀ : X i) (z : Σ j, X j)
    (hz : z ∈ Set.range (Sigma.mk i : X i → Σ j, X j)) :
    inclusion X i (decoder X i x₀ z) = z := by
  rcases hz with ⟨x, rfl⟩
  change Sigma.mk i (decoder X i x₀ (Sigma.mk i x)) = Sigma.mk i x
  exact congrArg (Sigma.mk i) (decoder_mk X i x₀ x)

/-- Every actual path from the selected original component stays in its clopen sigma range. -/
theorem path_mem_range (i : ι) (x : X i) {z : Σ j, X j}
    (p : Path (Sigma.mk i x) z) (t : I) :
    p t ∈ Set.range (Sigma.mk i : X i → Σ j, X j) := by
  have hRange : Set.range p ⊆ Set.range (Sigma.mk i : X i → Σ j, X j) :=
    (isPreconnected_range p.continuous).subset_isClopen
      (isClopen_range_sigmaMk (i := i))
      ⟨Sigma.mk i x, ⟨0, p.source⟩, ⟨x, rfl⟩⟩
  exact hRange (Set.mem_range_self t)

/-- An actual sigma path preserves its original index. -/
theorem path_index_eq {a b : Σ i, X i} (p : Path a b) : a.1 = b.1 := by
  rcases a with ⟨i, x⟩
  have hb := path_mem_range X i x p (1 : I)
  rw [p.target] at hb
  rcases hb with ⟨y, h⟩
  have hIndex := congrArg (fun z : Σ j, X j => z.1) h
  exact hIndex

/-- Every original sigma-groupoid arrow preserves the index of its endpoints. -/
theorem hom_index_eq {a b : FundamentalGroupoid (Σ i, X i)} (q : a ⟶ b) :
    a.as.1 = b.as.1 := by
  change Path.Homotopic.Quotient a.as b.as at q
  induction q using Path.Homotopic.Quotient.ind with
  | mk p => exact path_index_eq X p

/-- An actual sigma path between original component points is decoded with those same endpoints. -/
def decodePath (i : ι) (x₀ : X i) {x y : X i}
    (p : Path (Sigma.mk i x) (Sigma.mk i y)) : Path x y :=
  (p.map (decoder X i x₀).continuous).cast
    (decoder_mk X i x₀ x).symm (decoder_mk X i x₀ y).symm

/-- The decoded path uses the actual continuous decoder at every original time. -/
theorem decodePath_apply (i : ι) (x₀ : X i) {x y : X i}
    (p : Path (Sigma.mk i x) (Sigma.mk i y)) (t : I) :
    decodePath X i x₀ p t = decoder X i x₀ (p t) :=
  rfl

/-- Mapping and then decoding an original component path recovers that same actual path. -/
theorem decodePath_map (i : ι) (x₀ : X i) {x y : X i} (p : Path x y) :
    decodePath X i x₀ (p.map (inclusion X i).continuous) = p := by
  apply Path.ext
  funext t
  change decoder X i x₀ (inclusion X i (p t)) = p t
  exact decoder_inclusion X i x₀ (p t)

/-- Mapping an actual decoded sigma path recovers the same path in its original sigma component. -/
theorem map_decodePath (i : ι) (x₀ : X i) {x y : X i}
    (p : Path (Sigma.mk i x) (Sigma.mk i y)) :
    (decodePath X i x₀ p).map (inclusion X i).continuous = p := by
  apply Path.ext
  funext t
  change inclusion X i (decoder X i x₀ (p t)) = p t
  exact inclusion_decoder_of_mem_range X i x₀ (p t) (path_mem_range X i x p t)

/-- The original path-class decoder uses only the actual continuous decoder and endpoint casts. -/
def decodeClass (i : ι) (x₀ : X i) {x y : X i}
    (q : Path.Homotopic.Quotient (Sigma.mk i x) (Sigma.mk i y)) :
    Path.Homotopic.Quotient x y :=
  (q.map (decoder X i x₀)).cast
    (decoder_mk X i x₀ x).symm (decoder_mk X i x₀ y).symm

/-- The original class of an actual decoded path is the actual decoded original class. -/
theorem decodeClass_mk (i : ι) (x₀ : X i) {x y : X i}
    (p : Path (Sigma.mk i x) (Sigma.mk i y)) :
    decodeClass X i x₀ (Path.Homotopic.Quotient.mk p) =
      Path.Homotopic.Quotient.mk (decodePath X i x₀ p) := by
  rw [decodeClass, ← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast]
  rfl

/-- Decoding the class of an included original path class is the identity. -/
theorem decodeClass_map (i : ι) (x₀ : X i) {x y : X i}
    (q : Path.Homotopic.Quotient x y) :
    decodeClass X i x₀ (q.map (inclusion X i)) = q := by
  induction q using Path.Homotopic.Quotient.ind with
  | mk p =>
    change decodeClass X i x₀ (Path.Homotopic.Quotient.mk
      (p.map (inclusion X i).continuous)) = Path.Homotopic.Quotient.mk p
    exact (decodeClass_mk X i x₀ (p.map (inclusion X i).continuous)).trans
      (congrArg Path.Homotopic.Quotient.mk (decodePath_map X i x₀ p))

/-- Every original sigma path class between component points is recovered after decoding. -/
theorem map_decodeClass (i : ι) (x₀ : X i) {x y : X i}
    (q : Path.Homotopic.Quotient (Sigma.mk i x) (Sigma.mk i y)) :
    (decodeClass X i x₀ q).map (inclusion X i) = q := by
  induction q using Path.Homotopic.Quotient.ind with
  | mk p =>
    rw [decodeClass_mk, ← Path.Homotopic.Quotient.mk_map, map_decodePath]
    rfl

/-- The actual component inclusion induces a fully faithful original groupoid functor. -/
def fullyFaithful (i : ι) : (FundamentalGroupoid.map (inclusion X i)).FullyFaithful where
  preimage {a b} q := decodeClass X i a.as q
  map_preimage {a b} q := by
    change (decodeClass X i a.as q).map (inclusion X i) = q
    exact map_decodeClass X i a.as q
  preimage_map {a b} q := by
    change decodeClass X i a.as (q.map (inclusion X i)) = q
    exact decodeClass_map X i a.as q

/-- The functor preimage is the same original class decoder with the original source point. -/
theorem fullyFaithful_preimage (i : ι) {a b : FundamentalGroupoid (X i)}
    (q : (FundamentalGroupoid.map (inclusion X i)).obj a ⟶
      (FundamentalGroupoid.map (inclusion X i)).obj b) :
    (fullyFaithful X i).preimage q = decodeClass X i a.as q :=
  rfl

end FundamentalGroupoid.SigmaComponent

namespace FundamentalGroup

variable {ι : Type u} (X : ι → Type v) [∀ i, TopologicalSpace (X i)]

/-- The original based map of the sigma inclusion is bijective at its literal image basepoint. -/
theorem sigmaComponent_mapOfEq_bijective (i : ι) (x₀ : X i) :
    Function.Bijective (mapOfEq (FundamentalGroupoid.SigmaComponent.inclusion X i)
      (rfl : FundamentalGroupoid.SigmaComponent.inclusion X i x₀ = Sigma.mk i x₀)) := by
  rw [mapOfEq_rfl]
  exact ((FundamentalGroupoid.SigmaComponent.fullyFaithful X i).mulEquivEnd
    (FundamentalGroupoid.mk x₀)).bijective

/-- The constructed equivalence of the original component and sigma based End groups. -/
def sigmaComponentMulEquiv (i : ι) (x₀ : X i) :
    FundamentalGroup (X i) x₀ ≃* FundamentalGroup (Σ j, X j) (Sigma.mk i x₀) :=
  MulEquiv.ofBijective
    (mapOfEq (FundamentalGroupoid.SigmaComponent.inclusion X i)
      (rfl : FundamentalGroupoid.SigmaComponent.inclusion X i x₀ = Sigma.mk i x₀))
    (sigmaComponent_mapOfEq_bijective X i x₀)

/-- Its forward map is exactly the original sigma inclusion's equality-pointed homomorphism. -/
@[simp]
theorem sigmaComponentMulEquiv_apply (i : ι) (x₀ : X i) (q : FundamentalGroup (X i) x₀) :
    sigmaComponentMulEquiv X i x₀ q =
      mapOfEq (FundamentalGroupoid.SigmaComponent.inclusion X i)
        (rfl : FundamentalGroupoid.SigmaComponent.inclusion X i x₀ = Sigma.mk i x₀) q :=
  rfl

end FundamentalGroup

end

end
