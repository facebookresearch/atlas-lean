/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module

public import MathlibExt.AlgebraicGeometry.Sites.FieldModuleCohomologyCategory
public import MathlibExt.RepresentationTheory.Homological.ContCohomology.CoinducedRetractAcyclicity
public import MathlibExt.Algebra.Category.ModuleCat.Topology.Homology
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Continuous cohomology of injective discrete Galois modules

Let k and Ω be fields in universe u, with Ω a separable closure of k,
G = Gal(Ω/k), and c = max(u, w). A coefficient is a discrete abelian group
in universe c with continuous G-action. For an injective object I of
this action category, the equivariant constant-function map
I → C(G, I) splits in the same category.

The coinduced coefficient C(G, I) has the diagonal action
(g • φ)(x) = g • φ(g⁻¹x) and the compact-open topology.
Its comparison with the topological ℤ-representation preserves the
constant-function inclusion and the splitting. Thus Hⁿ_cts(G, I) is zero
for n > 0, and each closed homogeneous cochain in degree n + 1 is
the differential of a cochain in degree n.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe u w

namespace AlgebraicGeometry.Scheme.DerivedSections

attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, and put G = Gal(Ω/k) and c = max(u, w). Let D be the category
of discrete abelian groups in universe c with continuous G-action.
For I ∈ D, the discrete coinduced object viewed as a topological
ℤ-representation is isomorphic to C(G, I) with compact-open topology
and diagonal action (g • φ)(x) = g • φ(g⁻¹x).
The isomorphism preserves the underlying continuous functions. -/
def fieldCoinductionTopRepIso (I : FieldCohomologyModule.{u, w} k Ω) :
    DiscreteAbelianAction.toTopRep.obj (DiscreteAbelianAction.coind.{u, w}.obj I) ≅
      (DiscreteAbelianAction.toTopRep.obj I).coind₁ :=
  TopRep.toActionFromAction (DiscreteAbelianAction.toTopRep.obj I).coind₁

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, and put G = Gal(Ω/k) and c = max(u, w). Let D be the category
of discrete abelian groups in universe c with continuous G-action.
For I ∈ D, the discrete constant-function inclusion I → Coind(I),
followed by the coinduction comparison in topological ℤ-representations,
is the constant-function inclusion I → C(G, I). -/
theorem fieldCoinductionTopRepIso_iota (I : FieldCohomologyModule.{u, w} k Ω) :
    DiscreteAbelianAction.toTopRep.map (DiscreteAbelianAction.coindIota.{u, w}.app I) ≫
        (fieldCoinductionTopRepIso.{u, w} k Ω I).hom =
      TopRep.coind₁ι.app (DiscreteAbelianAction.toTopRep.obj I) := by
  rfl

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, and put G = Gal(Ω/k) and c = max(u, w). Let D be the category
of discrete abelian groups in universe c with continuous G-action.
If I is injective in D, this equivariant additive retraction
r : Coind(I) → I splits the constant-function inclusion i : I → Coind(I).
Injectivity is taken in the discrete continuous G-action category. -/
def fieldInjectiveCoinducedRetraction
    (I : FieldCohomologyModule.{u, w} k Ω) [Injective I] :
    DiscreteAbelianAction.coind.{u, w}.obj I ⟶ I :=
  Injective.factorThru (𝟙 I) (DiscreteAbelianAction.coindIota.{u, w}.app I)

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, and put G = Gal(Ω/k) and c = max(u, w). Let D be the category
of discrete abelian groups in universe c with continuous G-action.
For an injective I ∈ D, the coinduced retraction r and constant-function
inclusion i satisfy r ∘ i = id_I as morphisms of D. -/
theorem fieldInjectiveCoinduced_iota_retraction
    (I : FieldCohomologyModule.{u, w} k Ω) [Injective I] :
    DiscreteAbelianAction.coindIota.{u, w}.app I ≫
        fieldInjectiveCoinducedRetraction.{u, w} k Ω I = 𝟙 I :=
  Injective.comp_factorThru (𝟙 I) (DiscreteAbelianAction.coindIota.{u, w}.app I)

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, and put G = Gal(Ω/k) and c = max(u, w). Let D be the category
of discrete abelian groups in universe c with continuous G-action.
For an injective I ∈ D, the discrete equivariant retraction
Coind(I) → I gives a continuous equivariant map C(G, I) → I in
topological ℤ-representations, after the coinduction comparison. -/
def fieldInjectiveTopRepRetraction
    (I : FieldCohomologyModule.{u, w} k Ω) [Injective I] :
    (DiscreteAbelianAction.toTopRep.obj I).coind₁ ⟶
      DiscreteAbelianAction.toTopRep.obj I :=
  (fieldCoinductionTopRepIso.{u, w} k Ω I).inv ≫
    DiscreteAbelianAction.toTopRep.map (fieldInjectiveCoinducedRetraction.{u, w} k Ω I)

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, and put G = Gal(Ω/k) and c = max(u, w). Let D be the category
of discrete abelian groups in universe c with continuous G-action.
For an injective I ∈ D, the continuous equivariant retraction
s : C(G, I) → I satisfies s ∘ const = id_I in the topological
ℤ-representation category. -/
theorem fieldInjectiveTopRep_iota_retraction
    (I : FieldCohomologyModule.{u, w} k Ω) [Injective I] :
    TopRep.coind₁ι.app (DiscreteAbelianAction.toTopRep.obj I) ≫
        fieldInjectiveTopRepRetraction.{u, w} k Ω I =
      𝟙 (DiscreteAbelianAction.toTopRep.obj I) := by
  let P := DiscreteAbelianAction.toTopRep.{u, max u w} (G := Gal(Ω/k))
  let e := fieldCoinductionTopRepIso.{u, w} k Ω I
  let i := DiscreteAbelianAction.coindIota.{u, w}.app I
  let r := fieldInjectiveCoinducedRetraction.{u, w} k Ω I
  have hP : P.map i ≫ P.map r = 𝟙 (P.obj I) :=
    (P.map_comp i r).symm.trans
      ((congrArg P.map (fieldInjectiveCoinduced_iota_retraction.{u, w} k Ω I)).trans
        (P.map_id I))
  have hi : P.map i ≫ e.hom = TopRep.coind₁ι.app (P.obj I) :=
    fieldCoinductionTopRepIso_iota.{u, w} k Ω I
  change TopRep.coind₁ι.app (P.obj I) ≫ (e.inv ≫ P.map r) = 𝟙 (P.obj I)
  calc
    _ = (P.map i ≫ e.hom) ≫ (e.inv ≫ P.map r) :=
      congrArg (fun f => f ≫ (e.inv ≫ P.map r)) hi.symm
    _ = P.map i ≫ P.map r := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = 𝟙 (P.obj I) := hP

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, and put G = Gal(Ω/k) and c = max(u, w). Let D be the category
of discrete abelian groups in universe c with continuous G-action.
For an injective object I ∈ D and n ∈ ℕ, the continuous homogeneous
cohomology group Hⁿ⁺¹_cts(G, I) is a zero object.
 -/
theorem fieldInjectiveContinuousCohomology_succ_isZero
    (I : FieldCohomologyModule.{u, w} k Ω) [Injective I] (n : ℕ) :
    IsZero (continuousCohomology.{0, u, w} (n + 1)
      (DiscreteAbelianAction.toTopRep.obj I)) := by
  let : LocallyCompactSpace Gal(Ω/k) := by
    change LocallyCompactSpace (InfiniteGalois.profiniteGalGrp k Ω)
    infer_instance
  exact ContinuousCohomology.isZero_succ_of_coinduced_retract.{0, u, w}
    (DiscreteAbelianAction.toTopRep.obj I)
    (fieldInjectiveTopRepRetraction.{u, w} k Ω I)
    (fieldInjectiveTopRep_iota_retraction.{u, w} k Ω I) n

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, and put G = Gal(Ω/k) and c = max(u, w). Let D be the category
of discrete abelian groups in universe c with continuous G-action.
For an injective object I ∈ D, n ∈ ℕ and
x ∈ Hⁿ⁺¹_cts(G, I), one has x = 0. -/
theorem fieldInjectiveContinuousCohomology_eq_zero
    (I : FieldCohomologyModule.{u, w} k Ω) [Injective I] (n : ℕ)
    (x : continuousCohomology.{0, u, w} (n + 1)
      (DiscreteAbelianAction.toTopRep.obj I)) : x = 0 := by
  let A := continuousCohomology.{0, u, w} (n + 1)
    (DiscreteAbelianAction.toTopRep.obj I)
  have h : (𝟙 A : A ⟶ A) = 0 :=
    (fieldInjectiveContinuousCohomology_succ_isZero.{u, w} k Ω I n).eq_of_tgt _ _
  exact congrArg (fun f : A ⟶ A => f.hom x) h

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, and put G = Gal(Ω/k) and c = max(u, w). Let D be the category
of discrete abelian groups in universe c with continuous G-action.
For an injective object I ∈ D and n ∈ ℕ, let z be a closed
homogeneous continuous cochain in degree n + 1.
There exists a degree n cochain b with d(b) = z, where z is viewed
in the cochain term by the cycle inclusion. -/
theorem fieldInjectiveContinuousCohomology_cycle_boundary
    (I : FieldCohomologyModule.{u, w} k Ω) [Injective I] (n : ℕ)
    (z : (TopRep.homogeneousCochains (DiscreteAbelianAction.toTopRep.obj I)).cycles (n + 1)) :
    ∃ b : (TopRep.homogeneousCochains (DiscreteAbelianAction.toTopRep.obj I)).X n,
      ((TopRep.homogeneousCochains (DiscreteAbelianAction.toTopRep.obj I)).d n (n + 1)).hom b =
        ((TopRep.homogeneousCochains (DiscreteAbelianAction.toTopRep.obj I)).iCycles
          (n + 1)).hom z := by
  let K := TopRep.homogeneousCochains (DiscreteAbelianAction.toTopRep.obj I)
  have hz : K.homologyπ (n + 1) z = 0 :=
    fieldInjectiveContinuousCohomology_eq_zero.{u, w} k Ω I n _
  obtain ⟨b, hb⟩ :=
    (K.homologyπ_eq_zero_iff_exists_boundary n (n + 1) (by simp) z).mp hz
  exact ⟨b, hb.symm⟩

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, and put G = Gal(Ω/k) and c = max(u, w). Let D be the category
of discrete abelian groups in universe c with continuous G-action.
For an injective I ∈ D, this proposition records the monic
constant inclusion i, the discrete and topological coinduction
identifications, and their retractions r and s with r ∘ i = id and
s ∘ const = id. It also records preservation of the underlying function
and retraction values, vanishing of Hⁿ⁺¹_cts(G, I) for every n ∈ ℕ,
and the existence of a predecessor cochain b with d(b) = z for every
degree n + 1 cycle z. -/
def OriginalFieldInjectiveContinuousCochainAcyclicityLaws
    (I : FieldCohomologyModule.{u, w} k Ω) [Injective I] : Prop :=
  let P := DiscreteAbelianAction.toTopRep.{u, max u w} (G := Gal(Ω/k))
  let C := DiscreteAbelianAction.coind.{u, w} (G := Gal(Ω/k))
  let i := DiscreteAbelianAction.coindIota.{u, w}.app I
  let r := fieldInjectiveCoinducedRetraction.{u, w} k Ω I
  let e := fieldCoinductionTopRepIso.{u, w} k Ω I
  let s := fieldInjectiveTopRepRetraction.{u, w} k Ω I
  let K := TopRep.homogeneousCochains (P.obj I)
  Mono i ∧
  ((P.obj I).V : Type (max u w)) = DiscreteAbelianAction.underlying I ∧
  (DiscreteAbelianAction.underlying (C.obj I) : Type (max u w)) =
    C(Gal(Ω/k), DiscreteAbelianAction.underlying I) ∧
  (∀ (m : DiscreteAbelianAction.underlying I) (g : Gal(Ω/k)),
    DiscreteAbelianAction.coindFunction.{u, w} I (DiscreteAbelianAction.homToAdd i m) g = m) ∧
  i ≫ r = 𝟙 I ∧
  (∀ m : DiscreteAbelianAction.underlying (C.obj I),
    (P.map r).hom m = DiscreteAbelianAction.homToAdd r m) ∧
  P.map i ≫ e.hom = TopRep.coind₁ι.app (P.obj I) ∧
  TopRep.coind₁ι.app (P.obj I) ≫ s = 𝟙 (P.obj I) ∧
  (∀ n : ℕ, IsZero (continuousCohomology.{0, u, w} (n + 1) (P.obj I))) ∧
  ∀ (n : ℕ) (z : K.cycles (n + 1)),
    ∃ b : K.X n, (K.d n (n + 1)).hom b = (K.iCycles (n + 1)).hom z

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, and put G = Gal(Ω/k) and c = max(u, w). Let D be the category
of discrete abelian groups in universe c with continuous G-action.
Every injective I ∈ D has the stated coinduction identifications and
splittings in both the discrete action and topological representation
categories. In all positive degrees its continuous cohomology is zero,
and every homogeneous cycle has a predecessor whose differential is that cycle.
The coefficient groups have universe c, independently of the field universe u. -/
theorem original_field_injective_continuous_cochain_acyclicity
    (I : FieldCohomologyModule.{u, w} k Ω) [Injective I] :
    OriginalFieldInjectiveContinuousCochainAcyclicityLaws.{u, w} k Ω I := by
  refine ⟨inferInstance, DiscreteAbelianAction.toTopRep_obj I,
    DiscreteAbelianAction.coind_obj I, DiscreteAbelianAction.coindIota_apply I,
    fieldInjectiveCoinduced_iota_retraction.{u, w} k Ω I,
    (fun m => DiscreteAbelianAction.toTopRep_map_apply _ m),
    fieldCoinductionTopRepIso_iota.{u, w} k Ω I,
    fieldInjectiveTopRep_iota_retraction.{u, w} k Ω I,
    fieldInjectiveContinuousCohomology_succ_isZero.{u, w} k Ω I,
    fieldInjectiveContinuousCohomology_cycle_boundary.{u, w} k Ω I⟩

end AlgebraicGeometry.Scheme.DerivedSections
