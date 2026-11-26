/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicCurve_GluedPic0.lean`
and
`Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.DivisorClassGroup
public import MathlibExt.AlgebraicGeometry.Curve.PlaceEvaluation
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The glued degree-zero Picard group

Let `F` be a field extension of `K` and let `S` be a finite set of pairs `s = (P_s, Q_s)` of
`K`-rational places of `F` (`AlgebraicCurve.RationalPlace`), called nodes. Gluing data `(D₁, D₂, w)`
consists of two divisors `D₁` and `D₂` of `F` and a unit `w s` of `K` at each node. It is admissible
(`AlgebraicCurve.GluingData.admissible`) when `D₁` and `D₂` lie in
`AlgebraicCurve.GluingData.finiteDegZero`, `D₁` vanishes at each `P_s` and `D₂` vanishes at each
`Q_s`. It is glued principal (`AlgebraicCurve.GluingData.IsGluedPrincipal`) when it is
`(div g₁, div g₂, (g₁(P_s) / g₂(Q_s))_s)` for nonzero `g₁` and `g₂` in `F`, with values in the sense
of `AlgebraicCurve.Place.HasValueAt`. `AlgebraicCurve.GluedPic0 K F S` is the quotient of the
admissible subgroup by its intersection with the glued principal subgroup, so the class of
admissible data is zero exactly when the data is glued principal
(`AlgebraicCurve.GluedPic0.mk_eq_zero_iff`). Glued principal data need not be admissible: for
`F = L(t)` with `L` an infinite algebraic extension of `K` and no nodes, the divisor of `t` is
supported at two places with residue field `L`, so it does not lie in `finiteDegZero`.
`AlgebraicCurve.GluedPic0.toPic0Pair` sends a class to the classes of `D₁` and `D₂` in
`AlgebraicCurve.Pic0 K F`.

* At a `K`-rational place a function of order zero has a value in `Kˣ`, so the node units in `Kˣ`
  record every gluing relation: the classes whose two `Pic0` classes vanish are exactly the
  classes of node units (`AlgebraicCurve.GluedPic0.ker_toPic0Pair`), for every finite `S`.
* Admissible divisors are supported on places whose residue field is finite over `K`
  (`AlgebraicCurve.GluingData.finiteDegZero`). `AlgebraicCurve.Place.deg` is a `Module.finrank`,
  which is `0` for a residue field of infinite dimension over `K`, so only on such places does the
  degree of a divisor count its places with their residue degrees.

## Interpretation

The construction is motivated by the following geometric reading, which this file neither proves
nor uses: it builds no curves and compares nothing with line bundles. Suppose that `F` is the
function field of a smooth projective curve `C` over `K` and that the places in each projection of
`S` are distinct. Gluing two copies `C₁` and `C₂` of `C` by identifying the rational point `P_s` of
`C₁` with the rational point `Q_s` of `C₂` for each node gives a curve `X` with a node at each glued
point. Then `D₁` and `g₁` live on `C₁`, `D₂` and `g₂` live on `C₂`, and `GluedPic0 K F S` models the
group of line bundles on `X` of degree zero on each component, with `toPic0Pair` as restriction to
`C₁` and `C₂`. Gluing `P_s` to `Q_s` on a single copy of `C` gives a different group, with one
function and node values `g(P_s) / g(Q_s)`. That the places in each projection of `S` are distinct
is a condition on `S` alone; the definitions do not require it.
-/

@[expose] public section

noncomputable section

open IsLocalRing

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

@[simp]
private theorem ord_algebraMap_of_constant (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · have hu : IsUnit (algebraMap K v.toValuationSubring c) := hc.isUnit.map _
    have h := v.ord_coe_unit hu.unit
    rwa [IsUnit.unit_spec, coe_algebraMap] at h

private theorem hasValueAt_algebraMap (c : K) : v.HasValueAt (algebraMap K F c) c := by
  change algebraMap K F c - algebraMap K F c ∈ v.toValuationSubring.nonunits
  simp

theorem exists_isUnit_of_ord_eq_zero {f : F} (hf : f ≠ 0) (h : v.ord f = 0) :
    ∃ hm : f ∈ v.toValuationSubring, IsUnit (⟨f, hm⟩ : v.toValuationSubring) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [h, zpow_zero, mul_one] at hu
  subst hu
  exact ⟨(u : v.toValuationSubring).2, u.isUnit⟩

end Place

section Rational

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

/-- **Rational places.** The `K`-rational places of `F`: the places `v` with `v.IsRational`,
whose residue field is the image of `K`. -/
abbrev RationalPlace : Type _ :=
  {v : Place K F // v.IsRational}

variable {K F}

theorem RationalPlace.exists_hasValueAt_of_ord_eq_zero (v : RationalPlace K F) {g : F}
    (hg : g ≠ 0) (h : (v : Place K F).ord g = 0) : ∃ a : Kˣ, (v : Place K F).HasValueAt g a := by
  obtain ⟨hm, hu⟩ := (v : Place K F).exists_isUnit_of_ord_eq_zero hg h
  obtain ⟨a, ha⟩ := (v : Place K F).exists_hasValueAt v.2 hm
  refine ⟨Units.mk0 a fun h0 => (residue_ne_zero_iff_isUnit _).mpr hu ?_, ha⟩
  rw [((v : Place K F).hasValueAt_iff_residue hm a).mp ha, h0, map_zero]

end Rational

section Glued

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

/-- **Gluing data.** For a finite set `S` of pairs `s = (P_s, Q_s)` of `K`-rational places of `F`,
called nodes, gluing data is a pair of divisors `(D₁, D₂)` of `F` together with a unit of `K` at
each node. In the interpretation of `GluedPic0`, `D₁` and `D₂` are divisors on two curves with
function field `F` that are glued at the nodes; the definition itself involves no curves. -/
abbrev GluingData (S : Finset (RationalPlace K F × RationalPlace K F)) : Type _ :=
  Divisor K F × Divisor K F × (↥S → Additive Kˣ)

namespace GluingData

/-- **Degree-zero divisors on places of finite residue degree.** The divisors of degree zero
supported on places whose residue field is finite over `K`. On these places `Place.deg` is the
residue degree; at a place whose residue field has infinite dimension over `K`, the
`Module.finrank` defining `Place.deg` is `0`. -/
def finiteDegZero : AddSubgroup (Divisor K F) :=
  Divisor.degZero (K := K) (F := F) ⊓
    (Finsupp.supported ℤ ℤ {v : Place K F | Module.Finite K v.ResidueField}).toAddSubgroup

variable {K F}

theorem mem_finiteDegZero {D : Divisor K F} :
    D ∈ finiteDegZero K F ↔
      Divisor.degree D = 0 ∧ ∀ v ∈ D.support, Module.Finite K v.ResidueField :=
  Iff.rfl

theorem finiteDegZero_le_degZero : finiteDegZero K F ≤ Divisor.degZero (K := K) (F := F) :=
  inf_le_left

variable (S : Finset (RationalPlace K F × RationalPlace K F))

/-- **Admissible gluing data.** The subgroup of gluing data `(D₁, D₂, w)` such that `D₁` and `D₂`
lie in `finiteDegZero`, `D₁` vanishes at each `P_s` and `D₂` vanishes at each `Q_s`. -/
def admissible : AddSubgroup (GluingData K F S) where
  carrier := {x | x.1 ∈ finiteDegZero K F ∧ x.2.1 ∈ finiteDegZero K F ∧
    ∀ s ∈ S, x.1 s.1 = 0 ∧ x.2.1 s.2 = 0}
  zero_mem' := ⟨zero_mem _, zero_mem _, fun _ _ => ⟨rfl, rfl⟩⟩
  add_mem' := by
    rintro x y ⟨hx₁, hx₂, hx⟩ ⟨hy₁, hy₂, hy⟩
    refine ⟨add_mem hx₁ hy₁, add_mem hx₂ hy₂, fun s hs => ⟨?_, ?_⟩⟩
    · rw [Prod.fst_add, Finsupp.add_apply, (hx s hs).1, (hy s hs).1, add_zero]
    · rw [Prod.snd_add, Prod.fst_add, Finsupp.add_apply, (hx s hs).2, (hy s hs).2, add_zero]
  neg_mem' := by
    rintro x ⟨hx₁, hx₂, hx⟩
    refine ⟨neg_mem hx₁, neg_mem hx₂, fun s hs => ⟨?_, ?_⟩⟩
    · rw [Prod.fst_neg, Finsupp.neg_apply, (hx s hs).1, neg_zero]
    · rw [Prod.snd_neg, Prod.fst_neg, Finsupp.neg_apply, (hx s hs).2, neg_zero]

theorem mem_admissible {x : GluingData K F S} :
    x ∈ admissible S ↔ x.1 ∈ finiteDegZero K F ∧ x.2.1 ∈ finiteDegZero K F ∧
      ∀ s ∈ S, x.1 s.1 = 0 ∧ x.2.1 s.2 = 0 :=
  Iff.rfl

theorem zero_zero_mem_admissible (w : ↥S → Additive Kˣ) :
    ((0, 0, w) : GluingData K F S) ∈ admissible S :=
  ⟨zero_mem _, zero_mem _, fun _ _ => ⟨rfl, rfl⟩⟩

/-- **Glued principal gluing data.** Gluing data `(D₁, D₂, w)` is glued principal when there are
nonzero `g₁` and `g₂` in `F` such that `D₁` is the divisor of `g₁`, `D₂` is the divisor of `g₂`, and
the unit at each node `s` is the value of `g₁` at `P_s` divided by the value of `g₂` at `Q_s`. -/
def IsGluedPrincipal (x : GluingData K F S) : Prop :=
  ∃ (g₁ g₂ : F) (a b : ↥S → Kˣ), g₁ ≠ 0 ∧ g₂ ≠ 0 ∧
    (∀ v : Place K F, x.1 v = v.ord g₁) ∧ (∀ v : Place K F, x.2.1 v = v.ord g₂) ∧
    (∀ s : ↥S, ((s : RationalPlace K F × RationalPlace K F).1 : Place K F).HasValueAt g₁ (a s) ∧
      ((s : RationalPlace K F × RationalPlace K F).2 : Place K F).HasValueAt g₂ (b s)) ∧
    x.2.2 = fun s => Additive.ofMul (a s / b s)

/-- **Glued principal subgroup.** The subgroup of glued principal gluing data. -/
def gluedPrincipal : AddSubgroup (GluingData K F S) where
  carrier := {x | IsGluedPrincipal S x}
  zero_mem' := by
    refine ⟨1, 1, 1, 1, one_ne_zero, one_ne_zero, fun v => by simp, fun v => by simp,
      fun s => ⟨?_, ?_⟩, ?_⟩
    · simpa using
        ((s : RationalPlace K F × RationalPlace K F).1 : Place K F).hasValueAt_algebraMap 1
    · simpa using
        ((s : RationalPlace K F × RationalPlace K F).2 : Place K F).hasValueAt_algebraMap 1
    · funext s
      simp
  add_mem' := by
    rintro x y ⟨g₁, g₂, a, b, hg₁, hg₂, hx₁, hx₂, hv, hw⟩
      ⟨g₁', g₂', a', b', hg₁', hg₂', hy₁, hy₂, hv', hw'⟩
    refine ⟨g₁ * g₁', g₂ * g₂', a * a', b * b', mul_ne_zero hg₁ hg₁', mul_ne_zero hg₂ hg₂',
      fun v => ?_, fun v => ?_, fun s => ⟨?_, ?_⟩, ?_⟩
    · rw [Prod.fst_add, Finsupp.add_apply, hx₁ v, hy₁ v, v.ord_mul hg₁ hg₁']
    · rw [Prod.snd_add, Prod.fst_add, Finsupp.add_apply, hx₂ v, hy₂ v, v.ord_mul hg₂ hg₂']
    · simpa only [Pi.mul_apply, Units.val_mul] using
        Place.hasValueAt_mul _ (hv s).1 (hv' s).1
    · simpa only [Pi.mul_apply, Units.val_mul] using
        Place.hasValueAt_mul _ (hv s).2 (hv' s).2
    · rw [Prod.snd_add, Prod.snd_add, hw, hw']
      funext s
      rw [Pi.add_apply, Pi.mul_apply, Pi.mul_apply, ← ofMul_mul, div_mul_div_comm]
  neg_mem' := by
    rintro x ⟨g₁, g₂, a, b, hg₁, hg₂, hx₁, hx₂, hv, hw⟩
    refine ⟨g₁⁻¹, g₂⁻¹, a⁻¹, b⁻¹, inv_ne_zero hg₁, inv_ne_zero hg₂,
      fun v => ?_, fun v => ?_, fun s => ⟨?_, ?_⟩, ?_⟩
    · rw [Prod.fst_neg, Finsupp.neg_apply, hx₁ v, v.ord_inv]
    · rw [Prod.snd_neg, Prod.fst_neg, Finsupp.neg_apply, hx₂ v, v.ord_inv]
    · simpa only [Pi.inv_apply, Units.val_inv_eq_inv_val] using
        Place.hasValueAt_inv _ (hv s).1 (a s).ne_zero
    · simpa only [Pi.inv_apply, Units.val_inv_eq_inv_val] using
        Place.hasValueAt_inv _ (hv s).2 (b s).ne_zero
    · rw [Prod.snd_neg, Prod.snd_neg, hw]
      funext s
      rw [Pi.neg_apply, Pi.inv_apply, Pi.inv_apply, inv_div_inv, ← ofMul_inv, inv_div]

theorem mem_gluedPrincipal {x : GluingData K F S} :
    x ∈ gluedPrincipal S ↔ IsGluedPrincipal S x :=
  Iff.rfl

end GluingData

/-- **Glued degree-zero Picard group.** The quotient of the admissible subgroup of gluing data by
its intersection with the glued principal subgroup, for a finite set `S` of pairs `(P_s, Q_s)` of
`K`-rational places of `F`: the class of admissible data is zero exactly when the data is glued
principal (`GluedPic0.mk_eq_zero_iff`). Glued principal data that are not admissible, such as the
data of a function whose divisor has a place with residue field infinite over `K`, play no part.

Interpretation: when `F` is the function field of a smooth projective curve `C` over `K` and the
places in each projection of `S` are distinct, gluing two copies `C₁` and `C₂` of `C` by
identifying `P_s ∈ C₁` with `Q_s ∈ C₂` gives a curve `X` with a node at each glued point. Then `D₁`
and `g₁` live on `C₁`, `D₂` and `g₂` live on `C₂`, and the group models the line bundles on `X` of
degree zero on each component, with `toPic0Pair` as restriction to `C₁` and `C₂`. This
identification is an interpretation: the definition refers to no curves or line bundles, and
applies to any field extension `F` of `K` and any such `S`. -/
abbrev GluedPic0 (S : Finset (RationalPlace K F × RationalPlace K F)) : Type _ :=
  ↥(GluingData.admissible S) ⧸ (GluingData.gluedPrincipal S).addSubgroupOf (GluingData.admissible S)

namespace GluedPic0

variable {K F}
variable (S : Finset (RationalPlace K F × RationalPlace K F))

/-- **Quotient map.** The class of admissible gluing data in the glued Picard group. -/
def mk : ↥(GluingData.admissible S) →+ GluedPic0 K F S :=
  QuotientAddGroup.mk' _

theorem mk_surjective : Function.Surjective (mk S) :=
  QuotientAddGroup.mk'_surjective _

theorem mk_eq_zero_iff (x : ↥(GluingData.admissible S)) :
    mk S x = 0 ↔ GluingData.IsGluedPrincipal S (x : GluingData K F S) :=
  QuotientAddGroup.eq_zero_iff _

theorem mk_eq_mk_iff (x y : ↥(GluingData.admissible S)) :
    mk S x = mk S y ↔ GluingData.IsGluedPrincipal S (-(x : GluingData K F S) + y) :=
  QuotientAddGroup.eq

/-- **Picard classes of admissible gluing data.** The auxiliary map sending admissible gluing data
`(D₁, D₂, w)` to the classes of `D₁` and `D₂` in `Pic0 K F`. -/
def toPic0PairAux : ↥(GluingData.admissible S) →+ Pic0 K F × Pic0 K F where
  toFun x := (Pic0.mk ⟨(x : GluingData K F S).1, GluingData.finiteDegZero_le_degZero x.2.1⟩,
    Pic0.mk ⟨(x : GluingData K F S).2.1, GluingData.finiteDegZero_le_degZero x.2.2.1⟩)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- **Map to the pair of Picard groups.** The map from the glued Picard group to
`Pic0 K F × Pic0 K F` that sends the class of `(D₁, D₂, w)` to the classes of `D₁` and `D₂`; in the
interpretation of `GluedPic0`, restriction to the two components. -/
def toPic0Pair : GluedPic0 K F S →+ Pic0 K F × Pic0 K F :=
  QuotientAddGroup.lift _ (toPic0PairAux S) <| by
    rintro x ⟨g₁, g₂, _, _, hg₁, hg₂, h₁, h₂, -, -⟩
    rw [AddMonoidHom.mem_ker]
    exact Prod.ext ((QuotientAddGroup.eq_zero_iff _).mpr ⟨g₁, hg₁, h₁⟩)
      ((QuotientAddGroup.eq_zero_iff _).mpr ⟨g₂, hg₂, h₂⟩)

@[simp]
theorem toPic0Pair_mk (x : ↥(GluingData.admissible S)) :
    toPic0Pair S (mk S x) =
      (Pic0.mk ⟨(x : GluingData K F S).1, GluingData.finiteDegZero_le_degZero x.2.1⟩,
        Pic0.mk ⟨(x : GluingData K F S).2.1, GluingData.finiteDegZero_le_degZero x.2.2.1⟩) :=
  rfl

/-- **Node units as admissible data.** The auxiliary map sending a family `w` of node units to the
admissible gluing data `(0, 0, w)`. -/
def nodeUnitAux : (↥S → Additive Kˣ) →+ ↥(GluingData.admissible S) where
  toFun w := ⟨(0, 0, w), GluingData.zero_zero_mem_admissible S w⟩
  map_zero' := rfl
  map_add' _ _ := Subtype.ext <| Prod.ext (add_zero _).symm (Prod.ext (add_zero _).symm rfl)

/-- **Node-unit map.** The map sending a family `w` of node units to the class of `(0, 0, w)` in the
glued Picard group. -/
def nodeUnit : (↥S → Additive Kˣ) →+ GluedPic0 K F S :=
  (mk S).comp (nodeUnitAux S)

theorem nodeUnit_apply (w : ↥S → Additive Kˣ) :
    nodeUnit S w = mk S ⟨(0, 0, w), GluingData.zero_zero_mem_admissible S w⟩ :=
  rfl

@[simp]
theorem toPic0Pair_nodeUnit (w : ↥S → Additive Kˣ) : toPic0Pair S (nodeUnit S w) = 0 :=
  rfl

theorem toPic0Pair_comp_nodeUnit : (toPic0Pair S).comp (nodeUnit S) = 0 :=
  AddMonoidHom.ext (toPic0Pair_nodeUnit S)

theorem nodeUnit_const (c : Kˣ) : nodeUnit S (fun _ => Additive.ofMul c) = 0 := by
  rw [nodeUnit_apply, mk_eq_zero_iff]
  refine ⟨algebraMap K F c, 1, fun _ => c, 1, (map_ne_zero _).mpr c.ne_zero, one_ne_zero,
    fun v => by simp, fun v => by simp, fun s => ⟨?_, ?_⟩, ?_⟩
  · exact ((s : RationalPlace K F × RationalPlace K F).1 : Place K F).hasValueAt_algebraMap (c : K)
  · simpa using ((s : RationalPlace K F × RationalPlace K F).2 : Place K F).hasValueAt_algebraMap 1
  · funext s
    simp

/-- **Kernel of the map to the pair of Picard groups.** The kernel of `toPic0Pair` is the range of
`nodeUnit`: a class whose two divisors are principal is the class of a family of node units. This
uses that the places of the nodes are `K`-rational, and holds for every finite `S`, whether or not
the places in each projection of `S` are distinct. -/
theorem ker_toPic0Pair : (toPic0Pair S).ker = (nodeUnit S).range := by
  refine le_antisymm (fun z hz => ?_) ?_
  · obtain ⟨⟨⟨D₁, D₂, w⟩, hx⟩, rfl⟩ := mk_surjective S z
    have hS := hx.2.2
    rw [AddMonoidHom.mem_ker, toPic0Pair_mk, Prod.mk_eq_zero] at hz
    obtain ⟨g₁, hg₁, h₁⟩ := (QuotientAddGroup.eq_zero_iff _).mp hz.1
    obtain ⟨g₂, hg₂, h₂⟩ := (QuotientAddGroup.eq_zero_iff _).mp hz.2
    have h₁' : ∀ v : Place K F, D₁ v = v.ord g₁ := h₁
    have h₂' : ∀ v : Place K F, D₂ v = v.ord g₂ := h₂
    choose a ha using fun s : ↥S => (s : RationalPlace K F × RationalPlace K F).1
      |>.exists_hasValueAt_of_ord_eq_zero hg₁ ((h₁' _).symm.trans (hS s s.2).1)
    choose b hb using fun s : ↥S => (s : RationalPlace K F × RationalPlace K F).2
      |>.exists_hasValueAt_of_ord_eq_zero hg₂ ((h₂' _).symm.trans (hS s s.2).2)
    refine AddMonoidHom.mem_range.mpr ⟨w - fun s => Additive.ofMul (a s / b s), ?_⟩
    rw [nodeUnit_apply, mk_eq_mk_iff]
    refine ⟨g₁, g₂, a, b, hg₁, hg₂, fun v => ?_, fun v => ?_, fun s => ⟨ha s, hb s⟩, ?_⟩
    · simp [h₁' v]
    · simp [h₂' v]
    · simp
  · rintro _ ⟨w, rfl⟩
    exact toPic0Pair_nodeUnit S w

end GluedPic0

end Glued

end AlgebraicCurve
