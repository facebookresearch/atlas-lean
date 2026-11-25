/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import MathlibExt.AlgebraicGeometry.ExpandedRelativeFamilies
public import Mathlib.RingTheory.Localization.Basic

/-!
# Actual relative contact and pure node equations

Boundary contact is equality of the actual pulled Cartier ideal with
the product of actual marked-section ideals to their contact powers, on
every affine open. The node algebra is A[z1,z2]/(z1*z2-s), with native
etale/smooth chart homomorphisms. Pure contact is the source equation
w_i=z_sigma(i)^m h_i in the localization near the nodal ideal, with h_i
units and h1*h2 in the actual localized base ring.

This retains the normal-direction unit and base conditions; matching
orders on geometric points alone is insufficient. Source: Jun Li
arXiv:math/0110113v1, Definitions1.2/1.4, printed pp7--8;
arXiv:math/0009097v1, Definition2.3 and relative contact in Section4.3.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RelativeContactGeometry

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped BigOperators

def HasBoundaryContact {C X D T : Scheme.{0}} (f : C ⟶ X) (d : D ⟶ X)
    {r : ℕ} (marking : Fin r → (T ⟶ C)) (order : Fin r → ℕ) : Prop :=
  (∀ i, 0 < order i) ∧ ∀ U : C.affineOpens,
    (d.ker.comap f).ideal U = ∏ i : Fin r, ((marking i).ker.ideal U) ^ order i

def HasIndexedIdealContact {C X T : Scheme.{0}} (f : C ⟶ X) (I : X.IdealSheafData)
    {A : Type} [Fintype A] (marking : A → (T ⟶ C)) (order : A → ℕ) : Prop :=
  (∀ i, 0 < order i) ∧ ∀ U : C.affineOpens,
    (I.comap f).ideal U = ∏ i : A, ((marking i).ker.ideal U) ^ order i

def nodeRelation (A : Type) [CommRing A] (s : A) : MvPolynomial (Fin 2) A :=
  MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C s

abbrev NodeRing (A : Type) [CommRing A] (s : A) :=
  MvPolynomial (Fin 2) A ⧸ Ideal.span {nodeRelation A s}

def nodeCoefficient (A : Type) [CommRing A] (s : A) : A →+* NodeRing A s :=
  (Ideal.Quotient.mk _).comp MvPolynomial.C

def nodeVariable (A : Type) [CommRing A] (s : A) (i : Fin 2) : NodeRing A s :=
  Ideal.Quotient.mk _ (MvPolynomial.X i)

/-- Units in the residue along the entire nodal ideal form the actual
multiplicative system used in the source's pure-contact definition. -/
def unitsNearIdeal {A : Type} [CommRing A] (I : Ideal A) : Submonoid A where
  carrier := {a | IsUnit (Ideal.Quotient.mk I a)}
  one_mem' := by simp
  mul_mem' := by intro a b ha hb; simpa using ha.mul hb

abbrev NearIdeal {A : Type} [CommRing A] (I : Ideal A) := Localization (unitsNearIdeal I)

structure MappedNodeChart {C X T : Scheme.{0}} (p : C ⟶ T) (q : X ⟶ T)
    (f : C ⟶ X) (comm : f ≫ q = p) (x : C) where
  baseOpen : T.affineOpens
  sourceOpen : C.affineOpens
  targetOpen : X.affineOpens
  contains : x ∈ sourceOpen.val
  targetContains : f x ∈ targetOpen.val
  sourceOver : sourceOpen.val ≤ p ⁻¹ᵁ baseOpen.val
  targetOver : targetOpen.val ≤ q ⁻¹ᵁ baseOpen.val
  mapOver : sourceOpen.val ≤ f ⁻¹ᵁ targetOpen.val
  sourceVariable : Fin 2 → Γ(C, sourceOpen.val)
  targetVariable : Fin 2 → Γ(X, targetOpen.val)
  sourceParameter : Γ(T, baseOpen.val)
  targetParameter : Γ(T, baseOpen.val)
  sourceEquation : sourceVariable 0 * sourceVariable 1 =
    (p.appLE baseOpen.val sourceOpen.val sourceOver).hom sourceParameter
  targetEquation : targetVariable 0 * targetVariable 1 =
    (q.appLE baseOpen.val targetOpen.val targetOver).hom targetParameter
  sourceNode : x ∈ C.zeroLocus (U := sourceOpen.val) (Set.range sourceVariable)
  targetNode : f x ∈ X.zeroLocus (U := targetOpen.val) (Set.range targetVariable)
  sourceChart : NodeRing Γ(T, baseOpen.val) sourceParameter →+* Γ(C, sourceOpen.val)
  targetChart : NodeRing Γ(T, baseOpen.val) targetParameter →+* Γ(X, targetOpen.val)
  sourceCoefficient : ∀ a, sourceChart (nodeCoefficient _ sourceParameter a) =
    (p.appLE baseOpen.val sourceOpen.val sourceOver).hom a
  targetCoefficient : ∀ a, targetChart (nodeCoefficient _ targetParameter a) =
    (q.appLE baseOpen.val targetOpen.val targetOver).hom a
  sourceGenerator : ∀ i : Fin 2, sourceChart (nodeVariable _ sourceParameter i) = sourceVariable i
  targetGenerator : ∀ i : Fin 2, targetChart (nodeVariable _ targetParameter i) = targetVariable i
  etale : Etale (Spec.map (CommRingCat.ofHom sourceChart))
  smooth : Smooth (Spec.map (CommRingCat.ofHom targetChart))
  /-- The node locus of the source chart (inside the chart; `Scheme.zeroLocus` also contains the
  points outside it) is connected (Li, math/0110113v1, Def. 1.2). -/
  sourceNodeConnected : _root_.IsConnected
    ((sourceOpen.val : Set C) ∩ C.zeroLocus (U := sourceOpen.val) (Set.range sourceVariable))
  /-- The étale source chart induces an isomorphism of completions along the node (Li, Def. 1.2):
  an étale chart containing two lifts of the node (whose completion is a product) is excluded. -/
  sourceCompletion : letI := sourceChart.toAlgebra
    Function.Bijective (AdicCompletion.map
      (Ideal.span (Set.range (nodeVariable Γ(T, baseOpen.val) sourceParameter)))
      (Algebra.linearMap (NodeRing Γ(T, baseOpen.val) sourceParameter) Γ(C, sourceOpen.val)))

/-- General nodes are split only after these actual etale neighborhoods.
The common affine/open node equations above are imposed on the lifts. -/
structure EtaleNodePresentation {C X T : Scheme.{0}} (p : C ⟶ T) (q : X ⟶ T)
    (f : C ⟶ X) (comm : f ≫ q = p) (x : C) where
  base : Scheme.{0}
  source : Scheme.{0}
  target : Scheme.{0}
  baseMap : base ⟶ T
  sourceMap : source ⟶ C
  targetMap : target ⟶ X
  baseEtale : Etale baseMap
  sourceEtale : Etale sourceMap
  targetEtale : Etale targetMap
  sourceProjection : source ⟶ base
  targetProjection : target ⟶ base
  map : source ⟶ target
  sourceSquare : sourceMap ≫ p = sourceProjection ≫ baseMap
  targetSquare : targetMap ≫ q = targetProjection ≫ baseMap
  mapSquare : sourceMap ≫ f = map ≫ targetMap
  commutes : map ≫ targetProjection = sourceProjection
  point : source
  point_eq : sourceMap point = x
  chart : MappedNodeChart sourceProjection targetProjection map commutes point

variable {C X T : Scheme.{0}} {p : C ⟶ T} {q : X ⟶ T} {f : C ⟶ X}
  {comm : f ≫ q = p} {x : C} (N : MappedNodeChart p q f comm x)

def sourceIdeal : Ideal Γ(C, N.sourceOpen.val) := Ideal.span (Set.range N.sourceVariable)
def baseIdeal : Ideal Γ(T, N.baseOpen.val) := Ideal.span {N.sourceParameter}

/-- The localized base map is fixed on all actual base-ring generators. -/
structure LocalizedBaseMap where
  map : NearIdeal (baseIdeal N) →+* NearIdeal (sourceIdeal N)
  normalized : ∀ a : Γ(T, N.baseOpen.val),
    map (algebraMap Γ(T, N.baseOpen.val) (NearIdeal (baseIdeal N)) a) =
      algebraMap Γ(C, N.sourceOpen.val) (NearIdeal (sourceIdeal N))
        ((p.appLE N.baseOpen.val N.sourceOpen.val N.sourceOver).hom a)

structure PureContact (m : ℕ) where
  positive : 0 < m
  baseMap : LocalizedBaseMap N
  orientation : Fin 2 ≃ Fin 2
  unit : Fin 2 → (NearIdeal (sourceIdeal N))ˣ
  coefficient : NearIdeal (baseIdeal N)
  product : (unit 0 : NearIdeal (sourceIdeal N)) * (unit 1 : NearIdeal (sourceIdeal N)) =
    baseMap.map coefficient
  normalEquation : ∀ i : Fin 2,
    algebraMap Γ(C, N.sourceOpen.val) (NearIdeal (sourceIdeal N))
      ((f.appLE N.targetOpen.val N.sourceOpen.val N.mapOver).hom (N.targetVariable i)) =
    (algebraMap Γ(C, N.sourceOpen.val) (NearIdeal (sourceIdeal N))
      (N.sourceVariable (orientation i))) ^ m * (unit i : NearIdeal (sourceIdeal N))

end MathlibExt.AlgebraicGeometry.RelativeContactGeometry
