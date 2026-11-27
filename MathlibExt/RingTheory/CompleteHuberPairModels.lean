/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.Algebra.TopologicallyNilpotent
public import Mathlib.Topology.Algebra.GroupCompletion
public import MathlibExt.AlgebraicGeometry.AffineAdicSpectra

/-!
# Complete uniform Tate Huber pairs on actual rings

Boundedness is the neighborhood-of-zero multiplication criterion.
The powerbounded subring is characterized by that criterion on powers;
it cannot be an arbitrarily selected subring. The ring of definition is
an actual open subring with a finite ideal giving its adic topology.

The model permits direct reuse of completed local proofs while keeping
the same ring, plus ring, all-rank Spa and continuous maps. No new generic
gluing, powerboundedness or perfectoid theorem is requested here.

Sources: TauCetiProject/TauCeti at
`62bbc0596dc3539d488232e4e924a338548ea0a9`,
`TauCeti/RingTheory/Huber/{Bounded,PowerBounded,Basic}.lean` and
`TauCeti/RingTheory/Perfectoid/Basic.lean` (Apache 2.0);
Wedhorn, arXiv:1910.05934v1, Definitions 5.25, 6.1, 7.23;
Scholze, arXiv:1111.4914v1, Definition 1.6.
These are original source-characterized model interfaces, not copied
proof bodies or a claim that their providers have been ported.

Perfectoidness includes a genuine topologically nilpotent unit varpi
whose p-th power divides p inside the powerbounded subring. With this
ramification condition, the mod-p Frobenius test is the standard equivalent
criterion: Scholze, arXiv:1709.07343v4, Definition 3.1 and Remark 3.2;
TauCeti `Perfectoid/Basic.lean`,
`isPerfectoidTateRing_iff_frobenius_surjective_modP`. The mod-p test alone
would also hold for Q_p and is insufficient.
-/

@[expose] public noncomputable section

namespace MathlibExt.RingTheory.CompleteHuberPairModels

open CategoryTheory TopologicalSpace Filter
open MathlibExt.AlgebraicGeometry.AffineAdicSpectra
open scoped Topology

/-- Topological ring boundedness, with every zero neighborhood quantified. -/
def IsBoundedSet (A : Type) [CommRing A] [TopologicalSpace A]
    (S : Set A) : Prop :=
  ∀ U ∈ 𝓝 (0 : A), ∃ V ∈ 𝓝 (0 : A),
    ∀ v ∈ V, ∀ s ∈ S, v * s ∈ U

/-- Powerboundedness tests the actual set of nonnegative powers. -/
def IsPowerBounded (A : Type) [CommRing A] [TopologicalSpace A]
    (a : A) : Prop :=
  IsBoundedSet A (Set.range (fun n : ℕ ↦ a ^ n))

/-- A literal open adic ring of definition. -/
structure PairOfDefinition (A : Type) [CommRing A] [TopologicalSpace A] where
  ring : Subring A
  open_ring : IsOpen (ring : Set A)
  ideal : Ideal ring
  finite : ideal.FG
  adic : IsAdic ideal

/-- A complete uniform Tate Huber pair, with all geometry on its real ring. -/
structure HuberPair where
  ring : CommRingCat.{0}
  [uniformSpace : UniformSpace ring]
  [uniformAdd : IsUniformAddGroup ring]
  [topologicalRing : IsTopologicalRing ring]
  [complete : CompleteSpace ring]
  [hausdorff : T2Space ring]
  definition : PairOfDefinition ring
  powerbounded : Subring ring
  powerbounded_mem : ∀ a : ring, a ∈ powerbounded ↔ IsPowerBounded ring a
  uniform : IsBoundedSet ring (powerbounded : Set ring)
  plus : Subring ring
  plus_open : IsOpen (plus : Set ring)
  plus_integral : IsIntegrallyClosedIn plus ring
  plus_bound : plus ≤ powerbounded
  parameter : ringˣ
  parameter_nilpotent : IsTopologicallyNilpotent (parameter : ring)

attribute [instance] HuberPair.uniformSpace HuberPair.uniformAdd
  HuberPair.topologicalRing HuberPair.complete HuberPair.hausdorff

/-- The actual adic point space, retaining arbitrary valuation rank. -/
abbrev HuberPair.Space (P : HuberPair) := Spa P.plus

/-- A morphism of Huber pairs is a continuous plus-preserving ring map. -/
structure RingMap (P Q : HuberPair) where
  hom : P.ring →+* Q.ring
  continuous : Continuous hom
  plus : ∀ a ∈ P.plus, hom a ∈ Q.plus

/-- The actual contravariant all-rank Spa map. -/
def RingMap.spa {P Q : HuberPair} (f : RingMap P Q) : Q.Space → P.Space :=
  spaComap f.hom f.continuous f.plus

theorem RingMap.continuous_spa {P Q : HuberPair} (f : RingMap P Q) :
    Continuous f.spa := continuous_spaComap f.hom f.continuous f.plus

/-- The actual residue ring on which the perfectoid Frobenius is tested. -/
abbrev PerfectoidResidue (p : ℕ) (P : HuberPair) :=
  P.powerbounded ⧸ Ideal.span {(p : P.powerbounded)}

/-- The usual perfectoid criterion on a complete uniform Tate ring. -/
structure PerfectoidPair (p : ℕ) [Fact p.Prime] extends HuberPair where
  p_nilpotent : IsTopologicallyNilpotent (p : ring)
  pseudoUniformizer : ringˣ
  pseudoUniformizer_bound : (pseudoUniformizer : ring) ∈ powerbounded
  pseudoUniformizer_nilpotent :
    IsTopologicallyNilpotent (pseudoUniformizer : ring)
  pseudoUniformizer_divides :
    (⟨(pseudoUniformizer : ring), pseudoUniformizer_bound⟩ : powerbounded) ^ p ∣
      (p : powerbounded)
  frobenius_surjective : Function.Surjective
    (fun a : PerfectoidResidue p toHuberPair ↦ a ^ p)

/-- Characteristic-p affine perfectoid models on the same actual Huber pairs. -/
structure CharPPerfectoidPair (p : ℕ) [Fact p.Prime]
    extends PerfectoidPair p where
  [characteristic : CharP ring p]

attribute [instance] CharPPerfectoidPair.characteristic

variable (p : ℕ) [Fact p.Prime]

/-- Morphisms in the affine geometric category are opposite ring maps. -/
abbrev Hom (P Q : CharPPerfectoidPair p) :=
  RingMap Q.toHuberPair P.toHuberPair

@[ext] theorem RingMap.ext {P Q : HuberPair} (f g : RingMap P Q)
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance : Category (CharPPerfectoidPair p) where
  Hom := Hom p
  id P := ⟨RingHom.id _, continuous_id, fun _ h ↦ h⟩
  comp f g :=
    ⟨f.hom.comp g.hom, f.continuous.comp g.continuous,
      fun a h ↦ f.plus _ (g.plus _ h)⟩
  id_comp _ := by apply RingMap.ext; ext a; rfl
  comp_id _ := by apply RingMap.ext; ext a; rfl
  assoc _ _ _ := by apply RingMap.ext; ext a; rfl

/-- The actual point map of a geometric affine-perfectoid morphism. -/
def spaceMap {P Q : CharPPerfectoidPair p} (f : P ⟶ Q) :
    P.toHuberPair.Space → Q.toHuberPair.Space := f.spa

theorem continuous_spaceMap {P Q : CharPPerfectoidPair p} (f : P ⟶ Q) :
    Continuous (spaceMap p f) := f.continuous_spa

end MathlibExt.RingTheory.CompleteHuberPairModels
