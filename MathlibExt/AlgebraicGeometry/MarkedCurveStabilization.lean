/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

@[expose] public noncomputable section

/-!
# Stabilizing marked nodal families

All curves, markings and contractions are actual scheme morphisms.
Geometric nodality is tested by étale charts in the standard nodal curve.
Stability in characteristic zero is finite marked automorphisms of every
geometric fiber. The contraction records its genus-preserving structure-
sheaf images, marking equations and uniqueness among such stable models.

Source: Knudsen, The projectivity of the moduli space of stable curves II,
§1; Stacks Project, Tag 0E7N.
-/

namespace MathlibExt.AlgebraicGeometry.MarkedCurveStabilization

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

universe u

/-- The coordinate ring of the standard node. -/
abbrev NodeRing (k : Type u) [Field k] :=
  MvPolynomial (Fin 2) k ⧸
    (Ideal.span {MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)} :
      Ideal (MvPolynomial (Fin 2) k))

/-- The standard nodal curve over the field. -/
def nodeCurve (k : Type u) [Field k] : Over (Spec (.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (NodeRing k))))

/-- A curve is nodal if geometric closed points have actual nodal étale charts. -/
def IsNodal {k : Type u} [Field k] (C : Over (Spec (.of k))) : Prop :=
  ∀ x : C.left, IsClosed ({x} : Set C.left) →
    ∃ U : C.left.Opens, x ∈ U ∧
      ∃ f : U.toScheme ⟶ (nodeCurve k).left,
        Etale f ∧ f ≫ (nodeCurve k).hom = U.ι ≫ C.hom

/-- Marked automorphisms are actual automorphisms over the field. -/
abbrev MarkedAut {k : Type u} [Field k] (C : Over (Spec (.of k))) (n : ℕ)
    (p : Fin n → (Spec (.of k) ⟶ C.left)) :=
  {e : C ≅ C // ∀ i, p i ≫ e.hom.left = p i}

/-- The actual base-changed fiber over a field-valued point. -/
def fiberCurve {X S : Scheme.{u}} (f : X ⟶ S)
    {Ω : Type u} [Field Ω] (p : Spec (.of Ω) ⟶ S) : Over (Spec (.of Ω)) :=
  Over.mk (pullback.snd f p)

/-- A relative marking induces the displayed geometric fiber point. -/
def fiberMark {X S : Scheme.{u}} (f : X ⟶ S) (s : S ⟶ X) (hs : s ≫ f = 𝟙 S)
    {Ω : Type u} [Field Ω] (p : Spec (.of Ω) ⟶ S) :
    Spec (.of Ω) ⟶ (fiberCurve f p).left :=
  pullback.lift (p ≫ s) (𝟙 _) (by simp [Category.assoc, hs])

/-- A marked proper flat finitely presented nodal family of fixed genus. -/
structure MarkedFamily (S : Scheme.{u}) (n g : ℕ) where
  X : Scheme.{u}
  π : X ⟶ S
  [proper : IsProper π]
  [flat : Flat π]
  [finitePresentation : LocallyOfFinitePresentation π]
  marking : Fin n → (S ⟶ X)
  section_eq : ∀ i, marking i ≫ π = 𝟙 S
  disjoint : Pairwise fun i j ↦ Disjoint (Set.range (marking i)) (Set.range (marking j))
  smoothMarking : ∀ i, ∃ U : X.Opens, Smooth (U.ι ≫ π) ∧
    ∃ s : S ⟶ U.toScheme, s ≫ U.ι = marking i
  fibers : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (p : Spec (.of Ω) ⟶ S),
    GeometricallyConnected (fiberCurve π p).hom ∧
    IsNodal (fiberCurve π p) ∧ genus (fiberCurve π p).hom = g

/-- Fiberwise finite marked automorphisms, the characteristic-zero stability test. -/
def IsStable {S : Scheme.{u}} {n g : ℕ} (C : MarkedFamily S n g) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (p : Spec (.of Ω) ⟶ S),
    Finite (MarkedAut (fiberCurve C.π p) n
      (fun i ↦ fiberMark C.π (C.marking i) (C.section_eq i) p))

/-- Module-sheaf pushforward acts additively on the actual morphisms. -/
instance pushforward_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pushforward f).Additive where
  map_add := by
    intro M N a b
    rfl

/-- The contraction's structure-sheaf images use actual derived functors. -/
def IsGenusPreservingContraction {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  IsProper f ∧ Function.Surjective f ∧
    Nonempty (structureModule Y ≅ (Scheme.Modules.pushforward f).obj (structureModule X)) ∧
    IsZero (((Scheme.Modules.pushforward f).rightDerived 1).obj (structureModule X))

/-- Stabilization after forgetting the last marking and its unique stable model. -/
structure StabilizationModel {S : Scheme.{u}} (n g : ℕ) (C : MarkedFamily S (n + 1) g) where
  stabilized : MarkedFamily S n g
  stable : IsStable stabilized
  c : C.X ⟶ stabilized.X
  over : c ≫ stabilized.π = C.π
  markings : ∀ i : Fin n, C.marking i.castSucc ≫ c = stabilized.marking i
  contraction : IsGenusPreservingContraction c
  unique : ∀ (D : MarkedFamily S n g), IsStable D →
    ∀ f : C.X ⟶ D.X, f ≫ D.π = C.π →
      (∀ i : Fin n, C.marking i.castSucc ≫ f = D.marking i) →
      IsGenusPreservingContraction f →
        ∃! e : stabilized.X ≅ D.X,
          c ≫ e.hom = f ∧ e.hom ≫ D.π = stabilized.π

end MathlibExt.AlgebraicGeometry.MarkedCurveStabilization
