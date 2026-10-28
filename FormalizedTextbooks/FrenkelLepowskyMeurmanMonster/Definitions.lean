/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Statement skeleton for the FLM Monster finite-group milestones (T1–T6).

Status: specification with `sorry` holes plus proved framework material.
The six endpoint theorems live in `Milestones.lean`; this file holds the
shared construction interfaces they all refer to. The subgroup closure and
normality laws (former `F-*` holes) are proved, and `Q` is a genuine
concrete plus-type coordinate model (not the audited FLM group: the
model-to-FLM comparison is pending). No endpoint theorem is proved.

Provisional real-form convention: the Griess space is fixed as `Fin 196884 → ℝ`
(dimension and base field only). Product, form, and all FLM formulas are
explicit source-binding holes, each marked `TODO(S-*)` below.

Theorem/definition hole policy:
* `TODO(S-*)`: source-binding holes. The named object must be replaced by (or
  proved equal to) the audited FLM formula before endpoint proofs mean anything.
* `sorry` bodies on the six milestone theorems in `Milestones.lean`: proof holes.
* Former framework-law sorries (`F-*`): all discharged; the closure/normality
  proofs below are complete.
* The carriers of `leechIsomSubgroup` and `signsSubgroup` are genuine
  definitions (no `sorry` in the carrier data), and their closure/normality
  proofs are now proved as well.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Frattini
public import Mathlib.Algebra.Quotient
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.GroupTheory.Subgroup.Simple
public import MathlibExt.GroupTheory.NormalizedCocycleExtension

@[expose] public section

namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-! ## Griess algebra interface (fixed carrier, audited formulas pending) -/

/-- Fixed carrier: real 196884-dimensional space. Dimension and field only;
no product, form, or basis conventions are fixed by this abbreviation. -/
abbrev GriessSpace : Type := Fin 196884 → ℝ

/-- TODO(S-GriessProd): source-bind to the FLM Griess product formula
(including normalization). The product is a bilinear map; no associativity
(`Semiring`) or `AlgEquiv` structure is assumed. -/
noncomputable def griessProd :
    GriessSpace →ₗ[ℝ] GriessSpace →ₗ[ℝ] GriessSpace := by sorry

/-- TODO(S-GriessForm): source-bind to the FLM invariant bilinear form
(including normalization). -/
noncomputable def griessForm :
    GriessSpace →ₗ[ℝ] GriessSpace →ₗ[ℝ] ℝ := by sorry

/-- Genuine definition (no hole): a Griess automorphism is a linear
equivalence preserving BOTH the specified product and the specified form. -/
def IsGriessAuto (e : GriessSpace ≃ₗ[ℝ] GriessSpace) : Prop :=
  (∀ x y, e (griessProd x y) = griessProd (e x) (e y)) ∧
  (∀ x y, griessForm (e x) (e y) = griessForm x y)

/-- The product-and-form preserving subgroup of the ambient general linear
group. Genuine definition with proved closure laws (former framework holes
F-Aut*); the laws hold for the specified product/form ahead of source
binding. -/
noncomputable def griessAutSubgroup : Subgroup (GriessSpace ≃ₗ[ℝ] GriessSpace) :=
  { carrier := { e | IsGriessAuto e },
    one_mem' := ⟨fun _ _ => rfl, fun _ _ => rfl⟩,
    mul_mem' := by
      intro a b ha hb
      obtain ⟨hpa, hfa⟩ := ha
      obtain ⟨hpb, hfb⟩ := hb
      refine ⟨fun x y => ?_, fun x y => ?_⟩
      · change (a * b) (griessProd x y) = griessProd ((a * b) x) ((a * b) y)
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
          hpb, hpa]
      · change griessForm ((a * b) x) ((a * b) y) = griessForm x y
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hfa, hfb]
    inv_mem' := by
      intro a ha
      obtain ⟨hpa, hfa⟩ := ha
      refine ⟨fun x y => ?_, fun x y => ?_⟩
      · have h := hpa (a.symm x) (a.symm y)
        rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
        calc a.symm (griessProd x y)
            = a.symm (a (griessProd (a.symm x) (a.symm y))) := by rw [h]
          _ = griessProd (a.symm x) (a.symm y) :=
            LinearEquiv.symm_apply_apply a _
      · have h := hfa (a.symm x) (a.symm y)
        rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
        exact h.symm }

/-! ## Leech lattice and Co1 (lattice coordinates pending, shapes genuine) -/

/-- TODO(S-Leech): source-bind to the Leech lattice, as a `ℤ` submodule of
`Fin 24 → ℝ`. Only the ambient type is fixed by this declaration; WHICH
submodule is the hole. In particular, rank 24, integrality, evenness,
unimodularity, and minimum norm are unresolved source-definition properties:
they are NOT established by the bare `Submodule ℤ (Fin 24 → ℝ)` type. No
lattice coordinates are fabricated here. -/
noncomputable def LeechLattice : Submodule ℤ (Fin 24 → ℝ) := by sorry

/-- Genuine definition (no hole): the fixed standard Euclidean pairing on
`Fin 24 → ℝ`, the sum of coordinate products. -/
def stdPairingFun (x y : Fin 24 → ℝ) : ℝ :=
  Finset.sum Finset.univ (fun i => x i * y i)

/-- Genuine definition (no hole): a Leech isometry is an ambient real linear
equivalence preserving the standard coordinate pairing AND carrying
`LeechLattice` onto itself (membership equivalence for every vector). -/
def IsLeechIsom (e : (Fin 24 → ℝ) ≃ₗ[ℝ] (Fin 24 → ℝ)) : Prop :=
  (∀ x y, stdPairingFun (e x) (e y) = stdPairingFun x y) ∧
  (∀ x, x ∈ LeechLattice ↔ e x ∈ LeechLattice)

/-- The lattice-isometry subgroup of the ambient general linear group.
Carrier data are genuine (no `sorry`): pairing preservation plus
onto-`LeechLattice` membership. Closure laws are proved (former framework
holes F-LeechIsom*); they hold for any `LeechLattice` ahead of source
binding. Faithful only after `LeechLattice` is source-bound. -/
noncomputable def leechIsomSubgroup :
    Subgroup ((Fin 24 → ℝ) ≃ₗ[ℝ] (Fin 24 → ℝ)) :=
  { carrier := { e | IsLeechIsom e },
    one_mem' := ⟨fun _ _ => rfl, fun _ => Iff.rfl⟩,
    mul_mem' := by
      intro a b ha hb
      obtain ⟨hpa, haa⟩ := ha
      obtain ⟨hpb, hab⟩ := hb
      refine ⟨fun x y => ?_, fun x => ?_⟩
      · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hpa, hpb]
      · rw [LinearEquiv.mul_apply]
        exact (hab x).trans (haa (b x))
    inv_mem' := by
      intro a ha
      obtain ⟨hpa, haa⟩ := ha
      refine ⟨fun x y => ?_, fun x => ?_⟩
      · have h := hpa (a.symm x) (a.symm y)
        rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
        exact h.symm
      · change x ∈ LeechLattice ↔ a.symm x ∈ LeechLattice
        simpa using (haa (a.symm x)).symm }

/-- Genuine definition (no hole): the signs predicate inside the actual
isometry group. The first case is the underlying transformation `= 1`; the
second case sends every vector `x` to `-x` (stated pointwise to avoid any
negative-equiv API). -/
def IsSign (g : ↥leechIsomSubgroup) : Prop :=
  g.val = 1 ∨ ∀ x, g.val x = -x

/-- The `{±1}` subgroup of the actual isometry group. Carrier data are
genuine (no `sorry`): exactly the identity or the pointwise negative
identity. Closure proofs are proved (former framework holes F-signs*). -/
noncomputable def signsSubgroup : Subgroup ↥leechIsomSubgroup :=
  { carrier := { g | IsSign g },
    one_mem' := Or.inl rfl,
    mul_mem' := by
      intro a b ha hb
      obtain ha | ha := ha <;> obtain hb | hb := hb
      · refine Or.inl ?_
        change a.val * b.val = 1
        rw [ha, hb, mul_one]
      · refine Or.inr ?_
        intro x
        change (a.val * b.val) x = -x
        rw [ha, one_mul]
        exact hb x
      · refine Or.inr ?_
        intro x
        change (a.val * b.val) x = -x
        rw [hb, mul_one]
        exact ha x
      · refine Or.inl ?_
        change a.val * b.val = 1
        apply LinearEquiv.ext
        intro x
        rw [LinearEquiv.mul_apply, hb x, map_neg, ha x, neg_neg]
        simp only [LinearEquiv.coe_one, id_eq]
    inv_mem' := by
      intro a ha
      obtain ha | ha := ha
      · refine Or.inl ?_
        change (a.val)⁻¹ = 1
        rw [ha, inv_one]
      · refine Or.inr ?_
        intro x
        change a.val.symm x = -x
        have h1 : a.val (a.val.symm x) = a.val (-x) := by
          rw [LinearEquiv.apply_symm_apply, map_neg, ha x, neg_neg]
        exact a.val.injective h1 }

/-- Normality of the signs subgroup (former framework hole F-signsNormal),
discharged by direct conjugation computation: conjugating the identity or
the pointwise negative identity stays in `{±1}`. -/
noncomputable instance signsNormal : signsSubgroup.Normal := by
  constructor
  intro n hn g
  obtain hn | hn := hn
  · refine Or.inl ?_
    change g.val * n.val * (g.val)⁻¹ = 1
    rw [hn, mul_one, mul_inv_cancel]
  · refine Or.inr ?_
    intro x
    change (g.val * n.val * g.val.symm) x = -x
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hn,
      map_neg, LinearEquiv.apply_symm_apply]

/-- Genuine quotient shape: `Co1 = Isom(Λ)/{±1}`. Faithful only after
`LeechLattice` is source-bound (the isometry and signs carriers are already
genuine). -/
abbrev Co1 : Type := ↥leechIsomSubgroup ⧸ signsSubgroup

/-! ## Local subgroup data (FLM construction formulas pending) -/

/-! ### Concrete plus-type extraspecial coordinate model for `Q`

The FLM extraspecial group itself (hole S-Q) is still unaudited. What is
genuine here is a standard coordinate MODEL of shape `2₊^{1+24}`: the
normalized-cocycle extension of `F₂^24` by `F₂` seeded by the explicit
bilinear pairing `qBeta` below. Group laws come from the proved
`NormalizedCocycleExtension` instance, not from new proofs. The comparison
isomorphism between this model and the FLM group is PENDING (part of S-Q);
T1's claims about `Q` are now claims about the coordinate model. -/

/-- Additive coordinate pairing `β(v,w) = Σ_{i < 12} vᵢ * w_{i+12}` on
`F₂^24`: the first block is indexed by `Fin.castAdd`, the second by
`Fin.natAdd`. The bilinear seed of the plus-type cocycle. -/
def qBeta (v w : Fin 24 → ZMod 2) : ZMod 2 :=
  Finset.sum Finset.univ (fun i : Fin 12 => v (Fin.castAdd 12 i) * w (Fin.natAdd 12 i))

theorem qBeta_add_left (u v w : Fin 24 → ZMod 2) :
    qBeta (u + v) w = qBeta u w + qBeta v w := by
  simp [qBeta, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem qBeta_add_right (u v w : Fin 24 → ZMod 2) :
    qBeta u (v + w) = qBeta u v + qBeta u w := by
  simp [qBeta, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem qBeta_cocycle (u v w : Fin 24 → ZMod 2) :
    qBeta u v + qBeta (u + v) w = qBeta u (v + w) + qBeta v w := by
  rw [qBeta_add_left, qBeta_add_right, add_assoc]

theorem qBeta_zero_left (w : Fin 24 → ZMod 2) : qBeta 0 w = 0 := by
  simp [qBeta]

theorem qBeta_zero_right (v : Fin 24 → ZMod 2) : qBeta v 0 = 0 := by
  simp [qBeta]

theorem qBeta_smul_left (c : ZMod 2) (u w : Fin 24 → ZMod 2) :
    qBeta (c • u) w = c • qBeta u w := by
  have atom : ∀ i : Fin 12, ((c • u) (Fin.castAdd 12 i)) * w (Fin.natAdd 12 i)
      = c * (u (Fin.castAdd 12 i) * w (Fin.natAdd 12 i)) := by
    intro i
    rw [Pi.smul_apply, smul_eq_mul, mul_assoc]
  simp only [qBeta, atom, ← Finset.mul_sum, smul_eq_mul]

theorem qBeta_smul_right (c : ZMod 2) (u w : Fin 24 → ZMod 2) :
    qBeta u (c • w) = c • qBeta u w := by
  have atom : ∀ i : Fin 12, u (Fin.castAdd 12 i) * ((c • w) (Fin.natAdd 12 i))
      = c * (u (Fin.castAdd 12 i) * w (Fin.natAdd 12 i)) := by
    intro i
    rw [Pi.smul_apply, smul_eq_mul, mul_left_comm]
  simp only [qBeta, atom, ← Finset.mul_sum, smul_eq_mul]

/-- The coordinate pairing as a genuine `F₂`-bilinear map. -/
def qBilin : LinearMap.BilinMap (ZMod 2) (Fin 24 → ZMod 2) (ZMod 2) where
  toFun v :=
    { toFun := qBeta v
      map_add' := fun w w' => qBeta_add_right v w w'
      map_smul' := fun c w => qBeta_smul_right c v w }
  map_add' := fun u v => LinearMap.ext fun w => qBeta_add_left u v w
  map_smul' := fun c u => LinearMap.ext fun w => qBeta_smul_left c u w

/-- Normalized 2-cocycle seeding the extraspecial extension: the `qBeta`
values written multiplicatively. Normalization and the cocycle identity are
the additive abelian-group laws transported through `qBeta`-bilinearity. -/
def qCocycle : NormalizedCocycleExtension.NormalizedCocycle
    (Multiplicative (Fin 24 → ZMod 2)) (Multiplicative (ZMod 2)) where
  cocycle v w :=
    Multiplicative.ofAdd (qBeta (Multiplicative.toAdd v) (Multiplicative.toAdd w))
  one_left := by
    intro g
    rw [toAdd_one, qBeta_zero_left, ofAdd_zero]
  one_right := by
    intro g
    rw [toAdd_one, qBeta_zero_right, ofAdd_zero]
  cocycle_assoc := by
    intro v w z
    have h := qBeta_cocycle (Multiplicative.toAdd v) (Multiplicative.toAdd w)
      (Multiplicative.toAdd z)
    exact congrArg Multiplicative.ofAdd h

/-- Concrete plus-type extraspecial coordinate model: the normalized-cocycle
extension on `F₂^24` by `F₂`. The comparison with the FLM extraspecial
group is pending (part of S-Q) and is NOT proved here. -/
def Q : Type := NormalizedCocycleExtension.Extension qCocycle

/-- Group laws for the coordinate model, from the proved
`NormalizedCocycleExtension` instance. -/
instance instGroupQ : Group Q :=
  NormalizedCocycleExtension.instGroupExtension qCocycle

/-- TODO(S-H): source-bind type and group structure to the FLM extension group. -/
noncomputable def H : Type := by sorry

/-- TODO(S-H): group laws for the FLM extension group (part of S-H). -/
noncomputable instance instGroupH : Group H := by sorry

/-- Genuine: the center of `Q`, as a subgroup. -/
noncomputable def centerQ : Subgroup Q := Subgroup.center Q

/-- Normality of `centerQ` (former framework hole F-centerNormal), via the
Mathlib normal-center instance; this instance only fixes the name used by
the quotient below. -/
noncomputable instance centerQNormal : centerQ.Normal := Subgroup.instNormalCenter

/-- TODO(S-inclQ): source-bind to the FLM inclusion map `Q → H`. Raw map;
injectivity and image/kernel equality are proved in T1, not assumed here. -/
noncomputable def inclQ : Q →* H := by sorry

/-- TODO(S-projH): source-bind to the FLM projection map `H → Co1`. Raw map;
surjectivity and image/kernel equality are proved in T1, not assumed here. -/
noncomputable def projH : H →* Co1 := by sorry

/-- TODO(S-rho): source-bind to the FLM local action formulas. Raw map into
the ambient general linear group (NOT into `griessAutSubgroup`); injectivity
and product/form preservation are proved in T1, not assumed here. -/
noncomputable def rhoLocal : H →* (GriessSpace ≃ₗ[ℝ] GriessSpace) := by sorry

/-- TODO(S-sExtra): source-bind to the FLM extra symmetry transformation,
with its inverse. Raw ambient-GL element; preservation is proved in T2. -/
noncomputable def sExtra : GriessSpace ≃ₗ[ℝ] GriessSpace := by sorry

/-- Genuine definition (no endpoint conclusions built in): the concrete group
under study, generated by the local image and the extra symmetry. -/
noncomputable def G : Subgroup (GriessSpace ≃ₗ[ℝ] GriessSpace) :=
  Subgroup.closure (Set.range ⇑rhoLocal ∪ { sExtra })

/-! ## Extraspecial quadratic-form data (squares link pending) -/

/-- The coordinate projection `Q → F₂^24` (raw hom; kernel/range are T1
conclusions, not assumed here). Genuine: the proved `projHom` of the
coordinate model. The identification of the FLM quotient with this
projection is pending (part of S-qQuotHom). -/
def qQuotHom : Q →* Multiplicative (Fin 24 → ZMod 2) :=
  NormalizedCocycleExtension.projHom qCocycle

/-- TODO(S-centerMap): source-bind to the FLM identification of `Z(Q)` with
`F₂`, as a raw group hom. Bijectivity is proved in T1, not assumed here. -/
noncomputable def centerMap : ↥centerQ →* Multiplicative (ZMod 2) := by sorry

/-- The plus-type coordinate quadratic form: the diagonal `v ↦ β(v, v)` of
the coordinate pairing, as a genuine `QuadraticMap` via
`BilinMap.toQuadraticMap`. The proof that this form is the squares-induced
form (via `S-centerMap`) is pending and is recorded in T1's link equation;
that equation is NOT proved here. -/
def squareQuad :
    QuadraticMap (ZMod 2) (Fin 24 → ZMod 2) (ZMod 2) :=
  LinearMap.BilinMap.toQuadraticMap qBilin

/-- Genuine definition (no hole): the fixed hyperbolic plus-type model
`q(a,b) = Σᵢ aᵢ * bᵢ` on `F₂^12 ⊕ F₂^12`. -/
def hyperbolicFun (p : (Fin 12 → ZMod 2) × (Fin 12 → ZMod 2)) : ZMod 2 :=
  Finset.sum Finset.univ (fun i => p.1 i * p.2 i)

/-! ## Classical reference model (comparison route unresolved) -/

/-- TODO(S-classicalMonster): source-bind to an independently specified
classical Monster model (Griess, ATLAS, or other audited reference).
The historical comparison route is UNRESOLVED; this must NOT be defined as
`G`, and no isomorphism may be assumed here. T6 proves the isomorphism. -/
noncomputable def classicalMonster : Type := by sorry

/-- TODO(S-classicalMonster): group laws of the classical model (part of
S-classicalMonster). -/
noncomputable instance instGroupClassical : Group classicalMonster := by sorry

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
