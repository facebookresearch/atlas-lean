/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NonarchimedeanAnalyticSpaces
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Topology.Bases

/-!
# A rational-localization definition of the Berkovich structure presheaf

The local rings are actual quotients of restricted-series rings by the
relations `s T_i - t_i`. Their admissible Banach topology and unique bounded
restriction maps are explicit local dependencies. The corresponding
ordinary-open presheaf is the inverse limit of these rings on rational
domains contained in the open. This is a concrete compatible-family subring,
so its values, restrictions and constant sections are fixed constructions.

`RationalSpectrumGeometry` records the comparison of these local rings with
the weak real-seminorm spectrum. `AffinoidSheafGeometry` records the remaining
sheaf/local-ring proofs and evaluates every germ in the fixed rational-ring
point lying below it. Neither input replaces the rings or their maps.

TauCetiProject/TauCeti at revision
62bbc0596dc3539d488232e4e924a338548ea0a9 proves local strict rational-fraction
algebras and their classical-point universal property in
`TauCeti/RingTheory/Affinoid/RationalFraction.lean` and
`TauCeti/RingTheory/Affinoid/Subdomain/Rational/Basic.lean`, and continuous
adic restriction maps in
`TauCeti/AlgebraicGeometry/AdicSpace/Spa/Localization/PresentationIndependence.lean`.
Those are available local prerequisites. Their classical or valuative
topologies alone do not identify the weak Berkovich topology used here.

Reference: Berkovich, *Spectral theory and analytic geometry over
non-Archimedean fields*, §2.2; Zomervrucht, *Berkovich analytification*,
p. 1, the displayed formulas for `A_Z` and `𝒪_X(U)`.
https://www.mi.fu-berlin.de/math/groups/arithmetic_geometry/research_seminar/documents/berkovich03.pdf
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.BerkovichStructureSheaf

open CategoryTheory Opposite TopologicalSpace _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.NonarchimedeanAnalyticSpaces

variable {K : Type} [NormedField K] [IsUltrametricDist K]
  (A : AffinoidAlgebra K)

/-- Actual rational-domain data with arbitrary positive real radii. -/
structure RationalData where
  variableCount : ℕ
  radius : Fin variableCount → ℝ
  radius_pos : ∀ i, 0 < radius i
  denominator : A
  numerator : Fin variableCount → A
  unitIdeal : Ideal.span (insert denominator (Set.range numerator)) = ⊤

/-- The rational domain in the actual weak bounded-seminorm spectrum. -/
def rationalSet (D : RationalData A) : Set (BoundedPoint A) :=
  {p | p.seminorm D.denominator ≠ 0 ∧ ∀ i,
    p.seminorm (D.numerator i) ≤ D.radius i * p.seminorm D.denominator}

/-- The actual equations defining the rational fraction algebra. -/
def rationalIdeal (D : RationalData A) :
    Ideal (MvPowerSeries.Restricted A D.radius) :=
  Ideal.span (Set.range fun i ↦
    MvPowerSeries.Restricted.C D.radius D.denominator *
      MvPowerSeries.Restricted.X A D.radius i -
        MvPowerSeries.Restricted.C D.radius (D.numerator i))

/-- The actual rational fraction ring, before choosing its admissible norm. -/
abbrev RationalRing (D : RationalData A) :=
  MvPowerSeries.Restricted A D.radius ⧸ rationalIdeal A D

/-- A normalized Banach realization of this specified quotient ring. -/
structure RationalLocalization (D : RationalData A) where
  algebra : AffinoidAlgebra K
  [algebraOver : Algebra A algebra]
  [scalarTower : IsScalarTower K A algebra]
  quotientIso : RationalRing A D ≃ₐ[A] algebra
  norm_equivalent : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ b : algebra,
    c * sInf {v | ∃ f : MvPowerSeries.Restricted A D.radius,
      quotientIso (Ideal.Quotient.mk (rationalIdeal A D) f) = b ∧
        v = MvPowerSeries.gaussNorm (fun a : A ↦ ‖a‖) D.radius f.1} ≤ ‖b‖ ∧
    ‖b‖ ≤ C * sInf {v | ∃ f : MvPowerSeries.Restricted A D.radius,
      quotientIso (Ideal.Quotient.mk (rationalIdeal A D) f) = b ∧
        v = MvPowerSeries.gaussNorm (fun a : A ↦ ‖a‖) D.radius f.1}
  base_bound : ∃ C : ℝ, 0 < C ∧ ∀ a : A,
    ‖algebraMap A algebra a‖ ≤ C * ‖a‖

attribute [instance] RationalLocalization.algebraOver
  RationalLocalization.scalarTower

namespace RationalLocalization

variable {A} {D : RationalData A} (L : RationalLocalization A D)

/-- The fixed bounded base map is the actual quotient's coefficient map. -/
def baseMap : A ⟶ L.algebra where
  hom := IsScalarTower.toAlgHom K A L.algebra
  bound := L.base_bound

end RationalLocalization

/-- Explicit local dependencies: the specified quotient algebras, the
unique bounded restrictions, and their normalized maps on coefficients.
These are input constructors, separate from global analytic sheaf proofs. -/
structure RationalRestrictionTheory where
  localization : ∀ D : RationalData A, RationalLocalization A D
  restriction {D E : RationalData A} (h : rationalSet A E ⊆ rationalSet A D) :
    (localization D).algebra ⟶ (localization E).algebra
  restriction_base {D E : RationalData A}
      (h : rationalSet A E ⊆ rationalSet A D) :
    (restriction h).hom.comp (localization D).baseMap.hom =
      (localization E).baseMap.hom
  maps_ext (D : RationalData A) (B : AffinoidAlgebra K)
      (f g : (localization D).algebra ⟶ B)
      (h : f.hom.comp (localization D).baseMap.hom =
        g.hom.comp (localization D).baseMap.hom) : f = g

namespace RationalRestrictionTheory

variable {A} (R : RationalRestrictionTheory A)

theorem restriction_id (D : RationalData A) :
    R.restriction (Set.Subset.refl (rationalSet A D)) =
      𝟙 (R.localization D).algebra := by
  apply R.maps_ext
  exact (R.restriction_base _).trans (by ext a; rfl)

theorem restriction_comp {D E F : RationalData A}
    (h : rationalSet A E ⊆ rationalSet A D)
    (i : rationalSet A F ⊆ rationalSet A E) :
    R.restriction h ≫ R.restriction i = R.restriction (i.trans h) := by
  apply R.maps_ext
  change (R.restriction i).hom.comp
    ((R.restriction h).hom.comp (R.localization D).baseMap.hom) = _
  rw [R.restriction_base, R.restriction_base, R.restriction_base]

end RationalRestrictionTheory

variable {A} (R : RationalRestrictionTheory A)

/-- A rational domain contained in the specified actual ordinary open. -/
def Inside (U : Opens (spectrum A)) :=
  {D : RationalData A // rationalSet A D ⊆ (U : Set (spectrum A))}

/-- Compatible local sections: the actual inverse-limit subring. -/
def sections (U : Opens (spectrum A)) :
    Subring (∀ D : Inside U, (R.localization D.1).algebra) where
  carrier := {s | ∀ (D E : Inside U)
    (h : rationalSet A E.1 ⊆ rationalSet A D.1),
    (R.restriction h).hom (s D) = s E}
  zero_mem' := by intro D E h; exact map_zero (R.restriction h).hom
  one_mem' := by intro D E h; exact map_one (R.restriction h).hom
  add_mem' := by
    intro s t hs ht D E h
    change (R.restriction h).hom (s D + t D) = s E + t E
    rw [map_add, hs D E h, ht D E h]
  neg_mem' := by
    intro s hs D E h
    change (R.restriction h).hom (-s D) = -s E
    rw [map_neg, hs D E h]
  mul_mem' := by
    intro s t hs ht D E h
    change (R.restriction h).hom (s D * t D) = s E * t E
    rw [map_mul, hs D E h, ht D E h]

/-- Restriction is the actual projection of compatible families. -/
def restrict {U V : Opens (spectrum A)} (i : U ⟶ V) :
    sections R V →+* sections R U where
  toFun s := ⟨fun D ↦ s.1 ⟨D.1, D.2.trans i.le⟩,
    fun D E h ↦ s.2 ⟨D.1, D.2.trans i.le⟩ ⟨E.1, E.2.trans i.le⟩ h⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- The fixed rational-limit presheaf on the actual weak spectrum. -/
def presheaf : TopCat.Presheaf CommRingCat (spectrum A) where
  obj U := CommRingCat.of (sections R U.unop)
  map i := CommRingCat.ofHom (restrict R i.unop)
  map_id U := by ext s D; rfl
  map_comp i j := by ext s D; rfl

/-- Every algebra element defines the compatible family of its coefficients. -/
def constantSection (U : Opens (spectrum A)) : A →+* sections R U where
  toFun a := ⟨fun D ↦ (R.localization D.1).baseMap.hom a,
    fun D E h ↦ DFunLike.congr_fun (R.restriction_base h) a⟩
  map_zero' := by ext D; exact map_zero _
  map_one' := by ext D; exact map_one _
  map_add' _ _ := by ext D; exact map_add _ _ _
  map_mul' _ _ := by ext D; exact map_mul _ _ _

/-- Geometry comparing the actual rational rings with their real spectra. -/
structure RationalSpectrumGeometry where
  domainHomeomorph (D : RationalData A) :
    spectrum (R.localization D).algebra ≃ₜ rationalSet A D
  homeomorph_normalized (D : RationalData A)
      (p : BoundedPoint (R.localization D).algebra) :
    (domainHomeomorph D p).1 = comapPoint (R.localization D).baseMap p
  rationalBasis : IsTopologicalBasis
    (Set.range fun D : RationalData A ↦ interior (rationalSet A D))

variable (G : RationalSpectrumGeometry R)

/-- Data making the presheaf $\mathcal{O}$ on the Berkovich spectrum of $A$, whose sections over
an open $U$ are the compatible families of elements of the rational localizations $A_D$ for the
rational domains $D \subseteq U$, a locally ringed space with seminorms on its stalks:
$\mathcal{O}$ is a sheaf; every stalk $\mathcal{O}_p$ is a local ring with a multiplicative
seminorm $|\cdot|_p$ whose kernel is its maximal ideal; and for every section $s$ over $U$, every
point $p \in U$ and every rational domain $D \subseteq U$ containing $p$, the seminorm $|\cdot|_p$
of the germ of $s$ at $p$ is the seminorm at $p$, viewed as a point of the spectrum of $A_D$, of
the component of $s$ in $A_D$. -/
structure AffinoidSheafGeometry where
  isSheaf : (presheaf R).IsSheaf
  localRing : ∀ p : spectrum A, IsLocalRing ((presheaf R).stalk p)
  stalkNorm : ∀ p : spectrum A, MulRingSeminorm ((presheaf R).stalk p)
  support_maximal : ∀ (p : spectrum A) (s : (presheaf R).stalk p),
    stalkNorm p s = 0 ↔
      s ∈ @IsLocalRing.maximalIdeal ((presheaf R).stalk p) _ (localRing p)
  eval_germ (U : Opens (spectrum A)) (s : sections R U)
      (p : spectrum A) (hp : p ∈ U) (D : Inside U)
      (hD : p ∈ rationalSet A D.1) :
    stalkNorm p ((presheaf R).germ U p hp s) =
      ((G.domainHomeomorph D.1).symm ⟨p, hD⟩).seminorm (s.1 D)

namespace AffinoidSheafGeometry

variable {R G} (S : AffinoidSheafGeometry R G)

/-- The actual normalized affinoid locally ringed space. -/
def locallyRingedSpace : LocallyRingedSpace where
  carrier := spectrum A
  presheaf := presheaf R
  IsSheaf := S.isSheaf
  isLocalRing := S.localRing

end AffinoidSheafGeometry

end MathlibExt.AlgebraicGeometry.BerkovichStructureSheaf
