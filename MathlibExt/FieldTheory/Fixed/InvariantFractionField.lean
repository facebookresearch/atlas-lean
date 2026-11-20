/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_CerednikDrinfeld_MumfordQuotient.lean`,
`Definitions/Def_CerednikDrinfeld_MumfordQuotientNormalizer.lean`,
`Definitions/Def_CerednikDrinfeld_MumfordVertexType.lean`
and
`Definitions/Def_AlgebraicCurve_BaseChangeGalois.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
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

public import Mathlib.Algebra.Ring.Action.Group
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.Localization.FractionRing

import Mathlib.Tactic.Group

@[expose] public section

noncomputable section

namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

/-- The subgroup of pairs of ring automorphisms of `F` and `K` that agree on
the image of `K` in `F`: semilinear automorphisms of `F` over `K`. -/
def SemilinearAut : Subgroup (RingAut F × RingAut K) where
  carrier := {p | ∀ a : K, p.1 (algebraMap K F a) = algebraMap K F (p.2 a)}
  one_mem' _ := rfl
  mul_mem' := fun {p q} hp hq a => by
    show p.1 (q.1 (algebraMap K F a)) = algebraMap K F (p.2 (q.2 a))
    rw [hq a, hp (q.2 a)]
  inv_mem' := fun {p} hp a => by
    show p.1.symm (algebraMap K F a) = algebraMap K F (p.2.symm a)
    apply p.1.injective
    rw [RingEquiv.apply_symm_apply, hp (p.2.symm a), RingEquiv.apply_symm_apply]

namespace SemilinearAut

variable {K F}

theorem mem_iff {p : RingAut F × RingAut K} :
    p ∈ SemilinearAut K F ↔ ∀ a : K, p.1 (algebraMap K F a) = algebraMap K F (p.2 a) :=
  Iff.rfl

/-- The automorphism of `F` underlying a semilinear automorphism. -/
def toRingAut (g : SemilinearAut K F) : F ≃+* F := g.val.1

/-- The automorphism of the base field `K` underlying a semilinear
automorphism. -/
def baseAut (g : SemilinearAut K F) : K ≃+* K := g.val.2

theorem commutes (g : SemilinearAut K F) (a : K) :
    toRingAut g (algebraMap K F a) = algebraMap K F (baseAut g a) :=
  g.prop a

end SemilinearAut

end AlgebraicCurve

namespace CerednikDrinfeld.Mumford

section Generic

variable (K : Type*) [Field K] (G : Type*) [Group G] (M : Type*) [CommRing M] [Algebra K M]
variable [MulSemiringAction G M] [SMulCommClass G K M]

/-- The action of `g : G` on the fraction ring of `M`, induced by its action
on `M`. -/
def fracAct [IsDomain M] (g : G) : FractionRing M ≃+* FractionRing M :=
  IsFractionRing.ringEquivOfRingEquiv (MulSemiringAction.toRingEquiv G M g)

theorem fracAct_algebraMap [IsDomain M] (g : G) (m : M) :
    fracAct G M g (algebraMap M (FractionRing M) m) = algebraMap M (FractionRing M) (g • m) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ m

theorem fracAct_one [IsDomain M] : fracAct G M 1 = RingEquiv.refl _ := by
  apply RingEquiv.toRingHom_injective
  refine IsLocalization.ringHom_ext (nonZeroDivisors M) (RingHom.ext fun m => ?_)
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom]
  rw [fracAct_algebraMap, one_smul]; rfl

theorem fracAct_mul [IsDomain M] (g h : G) :
    fracAct G M (g * h) = (fracAct G M h).trans (fracAct G M g) := by
  apply RingEquiv.toRingHom_injective
  refine IsLocalization.ringHom_ext (nonZeroDivisors M) (RingHom.ext fun m => ?_)
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingEquiv.coe_trans]
  rw [fracAct_algebraMap, fracAct_algebraMap, fracAct_algebraMap, mul_smul]

scoped instance fracMulSemiringAction [IsDomain M] : MulSemiringAction G (FractionRing M) where
  smul g x := fracAct G M g x
  one_smul x := by show fracAct G M 1 x = x; rw [fracAct_one]; rfl
  mul_smul g h x := by
    show fracAct G M (g * h) x = fracAct G M g (fracAct G M h x); rw [fracAct_mul]; rfl
  smul_zero g := map_zero (fracAct G M g)
  smul_add g x y := map_add (fracAct G M g) x y
  smul_one g := map_one (fracAct G M g)
  smul_mul g x y := map_mul (fracAct G M g) x y

theorem frac_smul_def [IsDomain M] (g : G) (x : FractionRing M) :
    g • x = fracAct G M g x := rfl

theorem frac_smul_algebraMap [IsDomain M] (g : G) (m : M) :
    g • algebraMap M (FractionRing M) m = algebraMap M (FractionRing M) (g • m) :=
  fracAct_algebraMap G M g m

theorem smul_algebraMap_const_M (g : G) (c : K) :
    g • algebraMap K M c = algebraMap K M c := by
  rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]

theorem smul_algebraMap_const [IsDomain M] (g : G) (c : K) :
    g • algebraMap K (FractionRing M) c = algebraMap K (FractionRing M) c := by
  rw [IsScalarTower.algebraMap_apply K M (FractionRing M), frac_smul_algebraMap,
    smul_algebraMap_const_M]

scoped instance fracSMulCommClass [IsDomain M] : SMulCommClass G K (FractionRing M) :=
  ⟨fun g c x => by rw [Algebra.smul_def, Algebra.smul_def, smul_mul', smul_algebraMap_const]⟩

/-- The intermediate field of the fraction ring of `M` fixed by `G`. -/
def invariantIntermediateField [IsDomain M] : IntermediateField K (FractionRing M) :=
  FixedPoints.intermediateField G

/-- The subfield of the fraction ring of `M` fixed by `G`. -/
def invariantField [IsDomain M] : Subfield (FractionRing M) :=
  (invariantIntermediateField K G M).toSubfield

theorem mem_invariantField_iff [IsDomain M] (x : FractionRing M) :
    x ∈ invariantField K G M ↔ ∀ g : G, g • x = x := Iff.rfl

theorem mem_invariantIntermediateField_iff [IsDomain M] (x : FractionRing M) :
    x ∈ invariantIntermediateField K G M ↔ ∀ g : G, g • x = x := Iff.rfl

theorem invariantField_eq_fixedPoints [IsDomain M] :
    invariantField K G M = FixedPoints.subfield G (FractionRing M) := rfl

theorem coe_invariantIntermediateField [IsDomain M] :
    (invariantIntermediateField K G M : Set (FractionRing M)) = invariantField K G M := rfl

instance invariantFieldAlgebra [IsDomain M] : Algebra K ↥(invariantField K G M) :=
  (invariantIntermediateField K G M).algebra

/-- The intermediate field of the fraction ring of `M` fixed by a subgroup
`Γ` of `G`. -/
def invariantIntermediateFieldOf [IsDomain M] (Γ : Subgroup G) :
    IntermediateField K (FractionRing M) where
  carrier := {x | ∀ γ : G, γ ∈ Γ → γ • x = x}
  mul_mem' {x y} hx hy := fun γ hγ => by rw [smul_mul', hx γ hγ, hy γ hγ]
  one_mem' := fun γ _ => smul_one γ
  add_mem' {x y} hx hy := fun γ hγ => by rw [smul_add, hx γ hγ, hy γ hγ]
  zero_mem' := fun γ _ => smul_zero γ
  algebraMap_mem' c := fun γ _ => smul_algebraMap_const K G M γ c
  inv_mem' x hx := fun γ hγ => by rw [smul_inv'', hx γ hγ]

/-- The subfield of the fraction ring of `M` fixed by a subgroup `Γ` of `G`. -/
def invariantFieldOf [IsDomain M] (Γ : Subgroup G) : Subfield (FractionRing M) :=
  (invariantIntermediateFieldOf K G M Γ).toSubfield

theorem mem_invariantFieldOf_iff [IsDomain M] (Γ : Subgroup G) (x : FractionRing M) :
    x ∈ invariantFieldOf K G M Γ ↔ ∀ γ : G, γ ∈ Γ → γ • x = x := Iff.rfl

instance invariantFieldOfAlgebra [IsDomain M] (Γ : Subgroup G) :
    Algebra K ↥(invariantFieldOf K G M Γ) :=
  (invariantIntermediateFieldOf K G M Γ).algebra

theorem algebraMap_invariantFieldOf_coe [IsDomain M] (Γ : Subgroup G) (c : K) :
    ((algebraMap K ↥(invariantFieldOf K G M Γ) c : ↥(invariantFieldOf K G M Γ)) :
      FractionRing M) =
      algebraMap K (FractionRing M) c := rfl

theorem invariantFieldOf_top [IsDomain M] :
    invariantFieldOf K G M ⊤ = invariantField K G M :=
  Subfield.ext fun _ => ⟨fun h g => h g trivial, fun h g _ => h g⟩

theorem algebraMap_invariantField_coe [IsDomain M] (c : K) :
    ((algebraMap K ↥(invariantField K G M) c : ↥(invariantField K G M)) : FractionRing M) =
      algebraMap K (FractionRing M) c := rfl

theorem invariantFieldOf_mono_of_le [IsDomain M] {Γ Γ' : Subgroup G} (h : Γ' ≤ Γ) :
    invariantFieldOf K G M Γ ≤ invariantFieldOf K G M Γ' := fun _ hx γ hγ => hx γ (h hγ)

theorem invariantField_le_invariantFieldOf [IsDomain M] (Γ : Subgroup G) :
    invariantField K G M ≤ invariantFieldOf K G M Γ := fun _ hx γ _ => hx γ

/-- The action of `g : G` on the field fixed by a normal subgroup `N`,
as a ring equivalence. -/
def residualActRingEquiv [IsDomain M] (N : Subgroup G) [hN : N.Normal] (g : G) :
    ↥(invariantFieldOf K G M N) ≃+* ↥(invariantFieldOf K G M N) where
  toFun x := ⟨g • (x : FractionRing M), fun n hn => by
    rw [← mul_smul, show n * g = g * (g⁻¹ * n * g) from by group, mul_smul]
    congr 1
    exact x.2 (g⁻¹ * n * g) (by simpa using hN.conj_mem n hn g⁻¹)⟩
  invFun x := ⟨g⁻¹ • (x : FractionRing M), fun n hn => by
    rw [← mul_smul, show n * g⁻¹ = g⁻¹ * (g * n * g⁻¹) from by group, mul_smul]
    congr 1
    exact x.2 (g * n * g⁻¹) (hN.conj_mem n hn g)⟩
  left_inv x := Subtype.ext (inv_smul_smul g (x : FractionRing M))
  right_inv x := Subtype.ext (smul_inv_smul g (x : FractionRing M))
  map_mul' x y := Subtype.ext (smul_mul' g (x : FractionRing M) y)
  map_add' x y := Subtype.ext (smul_add g (x : FractionRing M) y)

theorem coe_residualActRingEquiv [IsDomain M] (N : Subgroup G) [N.Normal] (g : G)
    (x : ↥(invariantFieldOf K G M N)) :
    ((residualActRingEquiv K G M N g x : ↥(invariantFieldOf K G M N)) : FractionRing M) =
      g • (x : FractionRing M) := rfl

/-- The residual action of `G` on the field fixed by a normal subgroup `N`,
as `K`-algebra equivalences. -/
def residualAct [IsDomain M] (N : Subgroup G) [N.Normal] :
    G →* (↥(invariantFieldOf K G M N) ≃ₐ[K] ↥(invariantFieldOf K G M N)) where
  toFun g := AlgEquiv.ofRingEquiv (f := residualActRingEquiv K G M N g) (fun c =>
    Subtype.ext (by
      rw [coe_residualActRingEquiv]
      exact smul_algebraMap_const K G M g c))
  map_one' := AlgEquiv.ext fun x => Subtype.ext (one_smul G (x : FractionRing M))
  map_mul' g h := AlgEquiv.ext fun x => Subtype.ext (mul_smul g h (x : FractionRing M))

theorem coe_residualAct [IsDomain M] (N : Subgroup G) [N.Normal] (g : G)
    (x : ↥(invariantFieldOf K G M N)) :
    ((residualAct K G M N g x : ↥(invariantFieldOf K G M N)) : FractionRing M) =
      g • (x : FractionRing M) := rfl

theorem residualAct_eq_one_of_mem [IsDomain M] (N : Subgroup G) [N.Normal] {g : G}
    (hg : g ∈ N) :
    residualAct K G M N g = 1 :=
  AlgEquiv.ext fun x => Subtype.ext (x.2 g hg)

theorem mem_invariantField_iff_forall_residualAct [IsDomain M] (N : Subgroup G) [N.Normal]
    (x : ↥(invariantFieldOf K G M N)) :
    (x : FractionRing M) ∈ invariantField K G M ↔ ∀ g : G, residualAct K G M N g x = x :=
  ⟨fun h g => Subtype.ext (h g), fun h g => congrArg Subtype.val (h g)⟩

/-- A semilinear automorphism of `M` over `K` that commutes with the action
of `G`: a ring automorphism of `M` lying over a ring automorphism of `K`. -/
structure AmbientSemilinearAut where
  /-- The automorphism of the base field. -/
  base : K ≃+* K
  /-- The automorphism of `M`. -/
  map : M ≃+* M
  /-- The automorphism of `M` lies over the base automorphism. -/
  map_algebraMap : ∀ c : K, map (algebraMap K M c) = algebraMap K M (base c)
  /-- The automorphism of `M` commutes with the `G`-action. -/
  map_smul : ∀ (g : G) (m : M), map (g • m) = g • map m

namespace AmbientSemilinearAut

variable {K G M}

section Transport

omit [SMulCommClass G K M]

/-- The extension of an ambient semilinear automorphism to the fraction
ring of `M`. -/
def fracMap [IsDomain M] (s : AmbientSemilinearAut K G M) : FractionRing M ≃+* FractionRing M :=
  IsFractionRing.ringEquivOfRingEquiv s.map

theorem fracMap_algebraMap [IsDomain M] (s : AmbientSemilinearAut K G M) (m : M) :
    s.fracMap (algebraMap M (FractionRing M) m) = algebraMap M (FractionRing M) (s.map m) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ m

theorem fracMap_smul [IsDomain M] (s : AmbientSemilinearAut K G M) (g : G)
    (x : FractionRing M) :
    s.fracMap (g • x) = g • s.fracMap x := by
  have h : (s.fracMap.toRingHom.comp (fracAct G M g).toRingHom) =
      ((fracAct G M g).toRingHom.comp s.fracMap.toRingHom) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors M) (RingHom.ext fun m => ?_)
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom]
    rw [fracAct_algebraMap, fracMap_algebraMap, fracMap_algebraMap, fracAct_algebraMap,
      s.map_smul]
  exact congrArg (fun φ : FractionRing M →+* FractionRing M => φ x) h

theorem fracMap_algebraMap_const [IsDomain M] (s : AmbientSemilinearAut K G M) (c : K) :
    s.fracMap (algebraMap K (FractionRing M) c) = algebraMap K (FractionRing M) (s.base c) := by
  rw [IsScalarTower.algebraMap_apply K M (FractionRing M), fracMap_algebraMap, s.map_algebraMap,
    ← IsScalarTower.algebraMap_apply]

@[ext] theorem ext {s t : AmbientSemilinearAut K G M} (hb : s.base = t.base)
    (hm : s.map = t.map) : s = t := by
  cases s; cases t; congr

instance instGroup : Group (AmbientSemilinearAut K G M) where
  mul s t :=
    { base := t.base.trans s.base
      map := t.map.trans s.map
      map_algebraMap := fun c => by
        rw [RingEquiv.coe_trans, Function.comp_apply, t.map_algebraMap, s.map_algebraMap]; rfl
      map_smul := fun g m => by
        rw [RingEquiv.coe_trans, Function.comp_apply, t.map_smul, s.map_smul]; rfl }
  one :=
    { base := RingEquiv.refl K
      map := RingEquiv.refl M
      map_algebraMap := fun _ => rfl
      map_smul := fun _ _ => rfl }
  inv s :=
    { base := s.base.symm
      map := s.map.symm
      map_algebraMap := fun c => by
        apply s.map.injective
        rw [RingEquiv.apply_symm_apply, s.map_algebraMap, RingEquiv.apply_symm_apply]
      map_smul := fun g m => by
        apply s.map.injective
        rw [RingEquiv.apply_symm_apply, s.map_smul, RingEquiv.apply_symm_apply] }
  mul_assoc s t u := ext rfl rfl
  one_mul s := ext (RingEquiv.ext fun _ => rfl) (RingEquiv.ext fun _ => rfl)
  mul_one s := ext (RingEquiv.ext fun _ => rfl) (RingEquiv.ext fun _ => rfl)
  inv_mul_cancel s :=
    ext (RingEquiv.ext fun x => s.base.symm_apply_apply x)
      (RingEquiv.ext fun x => s.map.symm_apply_apply x)

@[simp] theorem base_mul (s t : AmbientSemilinearAut K G M) :
    (s * t).base = t.base.trans s.base := rfl

@[simp] theorem map_mul_eq (s t : AmbientSemilinearAut K G M) :
    (s * t).map = t.map.trans s.map := rfl

@[simp] theorem base_one : (1 : AmbientSemilinearAut K G M).base = RingEquiv.refl K := rfl

@[simp] theorem map_one_eq : (1 : AmbientSemilinearAut K G M).map = RingEquiv.refl M := rfl

theorem fracMap_one [IsDomain M] :
    (1 : AmbientSemilinearAut K G M).fracMap = RingEquiv.refl _ := by
  apply RingEquiv.toRingHom_injective
  refine IsLocalization.ringHom_ext (nonZeroDivisors M) (RingHom.ext fun m => ?_)
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom]
  rw [fracMap_algebraMap]; rfl

theorem fracMap_mul [IsDomain M] (s t : AmbientSemilinearAut K G M) :
    (s * t).fracMap = t.fracMap.trans s.fracMap := by
  apply RingEquiv.toRingHom_injective
  refine IsLocalization.ringHom_ext (nonZeroDivisors M) (RingHom.ext fun m => ?_)
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingEquiv.coe_trans]
  rw [fracMap_algebraMap, fracMap_algebraMap, fracMap_algebraMap]; rfl

end Transport

section Coeff

/-- The restriction of an ambient semilinear automorphism to the invariant
field, as a ring equivalence. -/
def invMap [IsDomain M] (s : AmbientSemilinearAut K G M) :
    ↥(invariantField K G M) ≃+* ↥(invariantField K G M) where
  toFun x := ⟨s.fracMap (x : FractionRing M), fun g => by rw [← fracMap_smul, x.2 g]⟩
  invFun x := ⟨s.fracMap.symm (x : FractionRing M), fun g => by
    apply s.fracMap.injective
    rw [fracMap_smul, RingEquiv.apply_symm_apply, x.2 g]⟩
  left_inv x := Subtype.ext (s.fracMap.symm_apply_apply (x : FractionRing M))
  right_inv x := Subtype.ext (s.fracMap.apply_symm_apply (x : FractionRing M))
  map_mul' x y := Subtype.ext (map_mul s.fracMap (x : FractionRing M) y)
  map_add' x y := Subtype.ext (map_add s.fracMap (x : FractionRing M) y)

/-- The semilinear automorphism of the invariant field induced by an
ambient semilinear automorphism. -/
def coeffAct [IsDomain M] (s : AmbientSemilinearAut K G M) :
    AlgebraicCurve.SemilinearAut K ↥(invariantField K G M) :=
  ⟨(s.invMap, s.base), fun c => Subtype.ext (by
    show s.fracMap (algebraMap K (FractionRing M) c) =
      ((algebraMap K ↥(invariantField K G M) (s.base c) : _) : FractionRing M)
    rw [fracMap_algebraMap_const]; rfl)⟩

theorem coeffAct_baseAut [IsDomain M] (s : AmbientSemilinearAut K G M) :
    AlgebraicCurve.SemilinearAut.baseAut (coeffAct s) = s.base := rfl

theorem coe_coeffAct_toRingAut [IsDomain M] (s : AmbientSemilinearAut K G M)
    (x : ↥(invariantField K G M)) :
    ((AlgebraicCurve.SemilinearAut.toRingAut (coeffAct s) x : ↥(invariantField K G M)) :
      FractionRing M) =
      s.fracMap (x : FractionRing M) := rfl

/-- The induced action on invariant fields, as a group homomorphism. -/
def coeffActHom [IsDomain M] :
    AmbientSemilinearAut K G M →* AlgebraicCurve.SemilinearAut K ↥(invariantField K G M) where
  toFun := coeffAct
  map_one' := Subtype.ext (Prod.ext (RingEquiv.ext fun x => Subtype.ext (by
    show (1 : AmbientSemilinearAut K G M).fracMap (x : FractionRing M) = x
    rw [fracMap_one]; rfl)) rfl)
  map_mul' s t := Subtype.ext (Prod.ext (RingEquiv.ext fun x => Subtype.ext (by
    show (s * t).fracMap (x : FractionRing M) = s.fracMap (t.fracMap (x : FractionRing M))
    rw [fracMap_mul]; rfl)) rfl)

@[simp] theorem coeffActHom_apply [IsDomain M] (s : AmbientSemilinearAut K G M) :
    coeffActHom s = coeffAct s := rfl

theorem coeffAct_comm_smul [IsDomain M] (s : AmbientSemilinearAut K G M) (g : G)
    (x : ↥(invariantField K G M)) :
    ((AlgebraicCurve.SemilinearAut.toRingAut (coeffAct s) x : ↥(invariantField K G M)) :
      FractionRing M) =
      s.fracMap (x : FractionRing M) ∧
    s.fracMap (g • (x : FractionRing M)) = g • s.fracMap (x : FractionRing M) :=
  ⟨rfl, fracMap_smul s g x⟩

theorem fracMap_comm_residualAct [IsDomain M] (s : AmbientSemilinearAut K G M)
    (N : Subgroup G) [N.Normal] (g : G)
    (x : ↥(invariantFieldOf K G M N)) :
    s.fracMap ((residualAct K G M N g x : ↥(invariantFieldOf K G M N)) : FractionRing M) =
      g • s.fracMap (x : FractionRing M) := by
  rw [coe_residualAct, fracMap_smul]

/-- The restriction of an ambient semilinear automorphism to the field
fixed by `Γ`, as a ring equivalence. -/
def invMapOf [IsDomain M] (Γ : Subgroup G) (s : AmbientSemilinearAut K G M) :
    ↥(invariantFieldOf K G M Γ) ≃+* ↥(invariantFieldOf K G M Γ) where
  toFun x := ⟨s.fracMap (x : FractionRing M), fun g hg => by rw [← fracMap_smul, x.2 g hg]⟩
  invFun x := ⟨s.fracMap.symm (x : FractionRing M), fun g hg => by
    apply s.fracMap.injective
    rw [fracMap_smul, RingEquiv.apply_symm_apply, x.2 g hg]⟩
  left_inv x := Subtype.ext (s.fracMap.symm_apply_apply (x : FractionRing M))
  right_inv x := Subtype.ext (s.fracMap.apply_symm_apply (x : FractionRing M))
  map_mul' x y := Subtype.ext (map_mul s.fracMap (x : FractionRing M) y)
  map_add' x y := Subtype.ext (map_add s.fracMap (x : FractionRing M) y)

theorem coe_invMapOf [IsDomain M] (Γ : Subgroup G) (s : AmbientSemilinearAut K G M)
    (x : ↥(invariantFieldOf K G M Γ)) :
    ((invMapOf Γ s x : ↥(invariantFieldOf K G M Γ)) : FractionRing M) =
      s.fracMap (x : FractionRing M) := rfl

/-- The semilinear automorphism of the `Γ`-fixed field induced by an
ambient semilinear automorphism. -/
def coeffActOf [IsDomain M] (Γ : Subgroup G) (s : AmbientSemilinearAut K G M) :
    AlgebraicCurve.SemilinearAut K ↥(invariantFieldOf K G M Γ) :=
  ⟨(invMapOf Γ s, s.base), fun c => Subtype.ext (by
    show s.fracMap (algebraMap K (FractionRing M) c) =
      ((algebraMap K ↥(invariantFieldOf K G M Γ) (s.base c) : _) : FractionRing M)
    rw [fracMap_algebraMap_const]; rfl)⟩

theorem coeffActOf_baseAut [IsDomain M] (Γ : Subgroup G) (s : AmbientSemilinearAut K G M) :
    AlgebraicCurve.SemilinearAut.baseAut (coeffActOf Γ s) = s.base := rfl

theorem coe_coeffActOf_toRingAut [IsDomain M] (Γ : Subgroup G) (s : AmbientSemilinearAut K G M)
    (x : ↥(invariantFieldOf K G M Γ)) :
    ((AlgebraicCurve.SemilinearAut.toRingAut (coeffActOf Γ s) x :
      ↥(invariantFieldOf K G M Γ)) : FractionRing M) =
      s.fracMap (x : FractionRing M) := rfl

/-- The induced action on `Γ`-fixed fields, as a group homomorphism. -/
def coeffActOfHom [IsDomain M] (Γ : Subgroup G) :
    AmbientSemilinearAut K G M →*
      AlgebraicCurve.SemilinearAut K ↥(invariantFieldOf K G M Γ) where
  toFun := coeffActOf Γ
  map_one' := Subtype.ext (Prod.ext (RingEquiv.ext fun x => Subtype.ext (by
    show (1 : AmbientSemilinearAut K G M).fracMap (x : FractionRing M) = x
    rw [fracMap_one]; rfl)) rfl)
  map_mul' s t := Subtype.ext (Prod.ext (RingEquiv.ext fun x => Subtype.ext (by
    show (s * t).fracMap (x : FractionRing M) = s.fracMap (t.fracMap (x : FractionRing M))
    rw [fracMap_mul]; rfl)) rfl)

@[simp] theorem coeffActOfHom_apply [IsDomain M] (Γ : Subgroup G)
    (s : AmbientSemilinearAut K G M) :
    coeffActOfHom Γ s = coeffActOf Γ s := rfl

theorem coeffActOf_comm_residualAct [IsDomain M] (N : Subgroup G) [N.Normal]
    (s : AmbientSemilinearAut K G M) (g : G)
    (x : ↥(invariantFieldOf K G M N)) :
    AlgebraicCurve.SemilinearAut.toRingAut (coeffActOf N s) (residualAct K G M N g x) =
      residualAct K G M N g (AlgebraicCurve.SemilinearAut.toRingAut (coeffActOf N s) x) :=
  Subtype.ext (by
    rw [coe_coeffActOf_toRingAut, coe_residualAct, coe_residualAct, coe_coeffActOf_toRingAut,
      fracMap_smul])

end Coeff

end AmbientSemilinearAut

section Normalizer

theorem smul_mem_invariantFieldOf_of_forall_mem [IsDomain M] (g : G) {Δ Δ' : Subgroup G}
    (h : ∀ d : G, d ∈ Δ' → g⁻¹ * d * g ∈ Δ) {x : FractionRing M}
    (hx : x ∈ invariantFieldOf K G M Δ) :
    g • x ∈ invariantFieldOf K G M Δ' := fun d hd => by
  rw [← mul_smul, show d * g = g * (g⁻¹ * d * g) from by group, mul_smul]
  congr 1
  exact hx (g⁻¹ * d * g) (h d hd)

theorem smul_mem_invariantFieldOf_of_mem_normalizer [IsDomain M] (Δ : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (Δ : Set G))
    {x : FractionRing M} (hx : x ∈ invariantFieldOf K G M Δ) :
    g • x ∈ invariantFieldOf K G M Δ :=
  smul_mem_invariantFieldOf_of_forall_mem K G M g
    (fun d hd => (Subgroup.mem_normalizer_iff''.1 hg d).1 hd) hx

/-- Transport of the `Δ`-fixed field to the `Δ'`-fixed field by conjugation
with `g`, as a ring equivalence, when conjugation by `g` carries `Δ'`
onto `Δ`. -/
def conjTransportRingEquiv [IsDomain M] (g : G) (Δ Δ' : Subgroup G)
    (h : ∀ d : G, d ∈ Δ' ↔ g⁻¹ * d * g ∈ Δ) :
    ↥(invariantFieldOf K G M Δ) ≃+* ↥(invariantFieldOf K G M Δ') where
  toFun x := ⟨g • (x : FractionRing M),
    smul_mem_invariantFieldOf_of_forall_mem K G M g (fun d hd => (h d).1 hd) x.2⟩
  invFun y := ⟨g⁻¹ • (y : FractionRing M),
    smul_mem_invariantFieldOf_of_forall_mem K G M g⁻¹ (fun d hd => (h (g⁻¹⁻¹ * d * g⁻¹)).2 (by
      simpa only [inv_inv, mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left, inv_mul_cancel,
        mul_one] using hd)) y.2⟩
  left_inv x := Subtype.ext (inv_smul_smul g (x : FractionRing M))
  right_inv y := Subtype.ext (smul_inv_smul g (y : FractionRing M))
  map_mul' x y := Subtype.ext (smul_mul' g (x : FractionRing M) y)
  map_add' x y := Subtype.ext (smul_add g (x : FractionRing M) y)

theorem coe_conjTransportRingEquiv [IsDomain M] (g : G) (Δ Δ' : Subgroup G)
    (h : ∀ d : G, d ∈ Δ' ↔ g⁻¹ * d * g ∈ Δ) (x : ↥(invariantFieldOf K G M Δ)) :
    ((conjTransportRingEquiv K G M g Δ Δ' h x : ↥(invariantFieldOf K G M Δ')) : FractionRing M) =
      g • (x : FractionRing M) := rfl

/-- Transport of the `Δ`-fixed field to the `Δ'`-fixed field by conjugation
with `g`, as a `K`-algebra equivalence. -/
def conjTransport [IsDomain M] (g : G) (Δ Δ' : Subgroup G)
    (h : ∀ d : G, d ∈ Δ' ↔ g⁻¹ * d * g ∈ Δ) :
    ↥(invariantFieldOf K G M Δ) ≃ₐ[K] ↥(invariantFieldOf K G M Δ') :=
  AlgEquiv.ofRingEquiv (f := conjTransportRingEquiv K G M g Δ Δ' h) (fun c => Subtype.ext (by
    rw [coe_conjTransportRingEquiv, algebraMap_invariantFieldOf_coe,
      algebraMap_invariantFieldOf_coe]
    exact smul_algebraMap_const K G M g c))

theorem coe_conjTransport [IsDomain M] (g : G) (Δ Δ' : Subgroup G)
    (h : ∀ d : G, d ∈ Δ' ↔ g⁻¹ * d * g ∈ Δ) (x : ↥(invariantFieldOf K G M Δ)) :
    ((conjTransport K G M g Δ Δ' h x : ↥(invariantFieldOf K G M Δ')) : FractionRing M) =
      g • (x : FractionRing M) :=
  rfl

theorem coe_conjTransport_symm [IsDomain M] (g : G) (Δ Δ' : Subgroup G)
    (h : ∀ d : G, d ∈ Δ' ↔ g⁻¹ * d * g ∈ Δ) (y : ↥(invariantFieldOf K G M Δ')) :
    (((conjTransport K G M g Δ Δ' h).symm y : ↥(invariantFieldOf K G M Δ)) : FractionRing M) =
      g⁻¹ • (y : FractionRing M) :=
  rfl

theorem mem_map_conj_iff (g : G) (Δ : Subgroup G) (d : G) :
    d ∈ Δ.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * d * g ∈ Δ := by
  constructor
  · rintro ⟨e, he, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using he
  · intro hd
    exact ⟨g⁻¹ * d * g, hd, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem mem_iff_of_mem_normalizer (Δ : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (Δ : Set G)) (d : G) :
    d ∈ Δ ↔ g⁻¹ * d * g ∈ Δ :=
  Subgroup.mem_normalizer_iff''.1 hg d

/-- The action of the normalizer of `Δ` on the `Δ`-fixed field, as
`K`-algebra equivalences. -/
def normalizerAct [IsDomain M] (Δ : Subgroup G) :
    ↥(Subgroup.normalizer (Δ : Set G)) →*
      (↥(invariantFieldOf K G M Δ) ≃ₐ[K] ↥(invariantFieldOf K G M Δ)) where
  toFun n := conjTransport K G M (n : G) Δ Δ (mem_iff_of_mem_normalizer G Δ n.2)
  map_one' := AlgEquiv.ext fun x => Subtype.ext (one_smul G (x : FractionRing M))
  map_mul' n n' :=
    AlgEquiv.ext fun x => Subtype.ext (mul_smul (n : G) (n' : G) (x : FractionRing M))

theorem coe_normalizerAct [IsDomain M] (Δ : Subgroup G)
    (n : ↥(Subgroup.normalizer (Δ : Set G))) (x : ↥(invariantFieldOf K G M Δ)) :
    ((normalizerAct K G M Δ n x : ↥(invariantFieldOf K G M Δ)) : FractionRing M) =
      (n : G) • (x : FractionRing M) :=
  rfl

theorem normalizerAct_eq_one_of_mem [IsDomain M] (Δ : Subgroup G)
    {n : ↥(Subgroup.normalizer (Δ : Set G))} (hn : (n : G) ∈ Δ) :
    normalizerAct K G M Δ n = 1 :=
  AlgEquiv.ext fun x => Subtype.ext (x.2 (n : G) hn)

theorem normalizerAct_eq_residualAct [IsDomain M] (N : Subgroup G) [N.Normal]
    (n : ↥(Subgroup.normalizer (N : Set G))) :
    normalizerAct K G M N n = residualAct K G M N (n : G) :=
  AlgEquiv.ext fun _ => Subtype.ext rfl

theorem coeffActOf_comm_conjTransport [IsDomain M] (s : AmbientSemilinearAut K G M) (g : G)
    (Δ Δ' : Subgroup G)
    (h : ∀ d : G, d ∈ Δ' ↔ g⁻¹ * d * g ∈ Δ) (x : ↥(invariantFieldOf K G M Δ)) :
    AlgebraicCurve.SemilinearAut.toRingAut (AmbientSemilinearAut.coeffActOf Δ' s)
        (conjTransport K G M g Δ Δ' h x) =
      conjTransport K G M g Δ Δ' h
        (AlgebraicCurve.SemilinearAut.toRingAut (AmbientSemilinearAut.coeffActOf Δ s) x) :=
  Subtype.ext (by
    rw [AmbientSemilinearAut.coe_coeffActOf_toRingAut, coe_conjTransport, coe_conjTransport,
      AmbientSemilinearAut.coe_coeffActOf_toRingAut, AmbientSemilinearAut.fracMap_smul])

theorem coeffActOf_comm_normalizerAct [IsDomain M] (s : AmbientSemilinearAut K G M)
    (Δ : Subgroup G)
    (n : ↥(Subgroup.normalizer (Δ : Set G))) (x : ↥(invariantFieldOf K G M Δ)) :
    AlgebraicCurve.SemilinearAut.toRingAut (AmbientSemilinearAut.coeffActOf Δ s)
        (normalizerAct K G M Δ n x) =
      normalizerAct K G M Δ n
        (AlgebraicCurve.SemilinearAut.toRingAut (AmbientSemilinearAut.coeffActOf Δ s) x) :=
  coeffActOf_comm_conjTransport K G M s (n : G) Δ Δ (mem_iff_of_mem_normalizer G Δ n.2) x

theorem coe_conjTransport_eq_of_le [IsDomain M] (g : G) {Δ₁ Δ₂ Δ₁' Δ₂' : Subgroup G}
    (h12 : Δ₂ ≤ Δ₁)
    (h₁ : ∀ d : G, d ∈ Δ₁' ↔ g⁻¹ * d * g ∈ Δ₁) (h₂ : ∀ d : G, d ∈ Δ₂' ↔ g⁻¹ * d * g ∈ Δ₂)
    (x : ↥(invariantFieldOf K G M Δ₁)) :
    ((conjTransport K G M g Δ₂ Δ₂' h₂ ⟨x, invariantFieldOf_mono_of_le K G M h12 x.2⟩ :
        ↥(invariantFieldOf K G M Δ₂')) :
        FractionRing M) =
      ((conjTransport K G M g Δ₁ Δ₁' h₁ x : ↥(invariantFieldOf K G M Δ₁')) : FractionRing M) :=
  rfl

end Normalizer

end Generic

section VertexType

variable {W : Type*} (𝒯 : SimpleGraph W) (w₀ : W)

/-- The type of a vertex `w` relative to a base vertex `w₀`: the parity of
the distance from `w₀` to `w`. -/
def vertexType (w : W) : ZMod 2 := (𝒯.dist w₀ w : ZMod 2)

theorem vertexType_apply (w : W) : vertexType 𝒯 w₀ w = (𝒯.dist w₀ w : ZMod 2) := rfl

@[simp] theorem vertexType_self : vertexType 𝒯 w₀ w₀ = 0 := by
  rw [vertexType, SimpleGraph.dist_self, Nat.cast_zero]

/-- The subgroup of `G` preserving the vertex type of every vertex. -/
def typePreserving (G : Type*) [Group G] [MulAction G W] (𝒯 : SimpleGraph W) (w₀ : W) :
    Subgroup G where
  carrier := {g | ∀ w : W, vertexType 𝒯 w₀ (g • w) = vertexType 𝒯 w₀ w}
  one_mem' := fun w => by rw [one_smul]
  mul_mem' {g h} hg hh := fun w => by rw [mul_smul, hg, hh]
  inv_mem' {g} hg := fun w => by rw [← hg (g⁻¹ • w), smul_inv_smul]

@[simp] theorem mem_typePreserving_iff {G : Type*} [Group G] [MulAction G W]
    (𝒯 : SimpleGraph W) (w₀ : W) (g : G) :
    g ∈ typePreserving G 𝒯 w₀ ↔ ∀ w : W, vertexType 𝒯 w₀ (g • w) = vertexType 𝒯 w₀ w :=
  Iff.rfl

end VertexType

section MumfordLayer

variable (K : Type*) [Field K] (G : Type*) [Group G] (M : Type*) [CommRing M] [IsDomain M]
variable [Algebra K M]
variable [MulSemiringAction G M] [SMulCommClass G K M]

/-- The invariant field, in the Mumford quotient layer. -/
abbrev mumfordField : Subfield (FractionRing M) := invariantField K G M

variable {W : Type*} [MulAction G W] (𝒯 : SimpleGraph W) (w₀ : W)

/-- There is an element of `G` exchanging the two vertex types. -/
def HasTypeExchanger : Prop := ∃ g : G, g ∉ typePreserving G 𝒯 w₀

/-- The field fixed by the type-preserving subgroup. -/
abbrev mumfordFieldPlus : Subfield (FractionRing M) :=
  invariantFieldOf K G M (typePreserving G 𝒯 w₀)

theorem mumfordField_le_mumfordFieldPlus : mumfordField K G M ≤ mumfordFieldPlus K G M 𝒯 w₀ :=
  invariantField_le_invariantFieldOf K G M _

/-- The residual action on the type-preserving fixed field. -/
abbrev exchangerAct [(typePreserving G 𝒯 w₀).Normal] :
    G →* (↥(mumfordFieldPlus K G M 𝒯 w₀) ≃ₐ[K] ↥(mumfordFieldPlus K G M 𝒯 w₀)) :=
  residualAct K G M (typePreserving G 𝒯 w₀)

theorem exchangerAct_eq_one_of_mem [(typePreserving G 𝒯 w₀).Normal] {g : G}
    (hg : g ∈ typePreserving G 𝒯 w₀) :
    exchangerAct K G M 𝒯 w₀ g = 1 :=
  residualAct_eq_one_of_mem K G M _ hg

end MumfordLayer

end CerednikDrinfeld.Mumford

end
