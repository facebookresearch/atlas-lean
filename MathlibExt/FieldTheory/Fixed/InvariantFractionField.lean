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
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import MathlibExt.Combinatorics.SimpleGraph.VertexType

import Mathlib.Tactic.Group

@[expose] public section

noncomputable section

namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

/-- **Semilinear automorphisms.** The subgroup of pairs of ring automorphisms of `F` and `K`
that agree on the image of `K` in `F`: semilinear automorphisms of `F` over `K`. -/
def SemilinearAut : Subgroup (RingAut F × RingAut K) where
  carrier := {p | ∀ a : K, p.1 (algebraMap K F a) = algebraMap K F (p.2 a)}
  one_mem' _ := rfl
  mul_mem' := fun {p q} hp hq a => by
    change p.1 (q.1 (algebraMap K F a)) = algebraMap K F (p.2 (q.2 a))
    rw [hq a, hp (q.2 a)]
  inv_mem' := fun {p} hp a => by
    change p.1.symm (algebraMap K F a) = algebraMap K F (p.2.symm a)
    apply p.1.injective
    rw [RingEquiv.apply_symm_apply, hp (p.2.symm a), RingEquiv.apply_symm_apply]

namespace SemilinearAut

variable {K F}

theorem mem_iff {p : RingAut F × RingAut K} :
    p ∈ SemilinearAut K F ↔ ∀ a : K, p.1 (algebraMap K F a) = algebraMap K F (p.2 a) :=
  Iff.rfl

/-- **Automorphism underlying a semilinear automorphism.** The automorphism of `F` underlying a
semilinear automorphism. -/
def toRingAut (g : SemilinearAut K F) : F ≃+* F := g.val.1

/-- **Base automorphism of a semilinear automorphism.** The automorphism of the base field `K`
underlying a semilinear automorphism. -/
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

/-- **Action on the fraction ring.** The action of `G` on the fraction ring of `M` induced by
its action on `M`, that is, Mathlib's `IsFractionRing.mulSemiringAction`. -/
scoped instance fracMulSemiringAction [IsDomain M] : MulSemiringAction G (FractionRing M) :=
  IsFractionRing.mulSemiringAction G M (FractionRing M)

/-- **Commutation with the scalars.** The induced action commutes with the scalars of `K`, by
Mathlib's `IsFractionRing.smulCommClass`. -/
scoped instance fracSMulCommClass [IsDomain M] : SMulCommClass G K (FractionRing M) :=
  IsFractionRing.smulCommClass G K M K (FractionRing M)

/-- **Residual action of an element.** The action of `g : G` on the field fixed by a normal
subgroup `N`, as a ring equivalence. -/
def residualActRingEquiv [IsDomain M] (N : Subgroup G) [hN : N.Normal] (g : G) :
    (FixedPoints.intermediateField N : IntermediateField K (FractionRing M)) ≃+*
      (FixedPoints.intermediateField N : IntermediateField K (FractionRing M)) where
  toFun x := ⟨g • (x : FractionRing M), fun n => by
    change (n : G) • g • (x : FractionRing M) = g • (x : FractionRing M)
    rw [← mul_smul, show (n : G) * g = g * (g⁻¹ * n * g) from by group, mul_smul]
    congr 1
    exact x.2 ⟨g⁻¹ * n * g, by simpa using hN.conj_mem n n.2 g⁻¹⟩⟩
  invFun x := ⟨g⁻¹ • (x : FractionRing M), fun n => by
    change (n : G) • g⁻¹ • (x : FractionRing M) = g⁻¹ • (x : FractionRing M)
    rw [← mul_smul, show (n : G) * g⁻¹ = g⁻¹ * (g * n * g⁻¹) from by group, mul_smul]
    congr 1
    exact x.2 ⟨g * n * g⁻¹, hN.conj_mem n n.2 g⟩⟩
  left_inv x := Subtype.ext (inv_smul_smul g (x : FractionRing M))
  right_inv x := Subtype.ext (smul_inv_smul g (x : FractionRing M))
  map_mul' x y := Subtype.ext (smul_mul' g (x : FractionRing M) y)
  map_add' x y := Subtype.ext (smul_add g (x : FractionRing M) y)

theorem coe_residualActRingEquiv [IsDomain M] (N : Subgroup G) [N.Normal] (g : G)
    (x : FixedPoints.intermediateField N) :
    ((residualActRingEquiv K G M N g x :
      (FixedPoints.intermediateField N : IntermediateField K (FractionRing M))) :
        FractionRing M) =
      g • (x : FractionRing M) := rfl

/-- **Residual action.** The action of `G` on the field fixed by a normal subgroup `N`, as
`K`-algebra equivalences. -/
def residualAct [IsDomain M] (N : Subgroup G) [N.Normal] :
    G →* ((FixedPoints.intermediateField N : IntermediateField K (FractionRing M)) ≃ₐ[K]
      (FixedPoints.intermediateField N : IntermediateField K (FractionRing M))) where
  toFun g := AlgEquiv.ofRingEquiv (f := residualActRingEquiv K G M N g) (fun c =>
    Subtype.ext (by
      rw [coe_residualActRingEquiv]
      exact smul_algebraMap g c))
  map_one' := AlgEquiv.ext fun x => Subtype.ext (one_smul G (x : FractionRing M))
  map_mul' g h := AlgEquiv.ext fun x => Subtype.ext (mul_smul g h (x : FractionRing M))

theorem coe_residualAct [IsDomain M] (N : Subgroup G) [N.Normal] (g : G)
    (x : FixedPoints.intermediateField N) :
    ((residualAct K G M N g x :
      (FixedPoints.intermediateField N : IntermediateField K (FractionRing M))) :
        FractionRing M) =
      g • (x : FractionRing M) := rfl

theorem residualAct_eq_one_of_mem [IsDomain M] (N : Subgroup G) [N.Normal] {g : G}
    (hg : g ∈ N) :
    residualAct K G M N g = 1 :=
  AlgEquiv.ext fun x => Subtype.ext (x.2 ⟨g, hg⟩)

theorem mem_fixedPoints_iff_forall_residualAct [IsDomain M] (N : Subgroup G) [N.Normal]
    (x : (FixedPoints.intermediateField N : IntermediateField K (FractionRing M))) :
    (x : FractionRing M) ∈
        (FixedPoints.intermediateField G : IntermediateField K (FractionRing M)) ↔
      ∀ g : G, residualAct K G M N g x = x :=
  ⟨fun h g => Subtype.ext (h g), fun h g => congrArg Subtype.val (h g)⟩

/-- **Ambient semilinear automorphism.** A semilinear automorphism of `M` over `K` that
commutes with the action of `G`: a ring automorphism of `M` lying over a ring automorphism of
`K`. -/
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

/-- **Extension to the fraction ring.** The extension of an ambient semilinear automorphism to
the fraction ring of `M`. -/
def fracMap (s : AmbientSemilinearAut K G M) : FractionRing M ≃+* FractionRing M :=
  IsFractionRing.ringEquivOfRingEquiv s.map

theorem fracMap_algebraMap (s : AmbientSemilinearAut K G M) (m : M) :
    s.fracMap (algebraMap M (FractionRing M) m) = algebraMap M (FractionRing M) (s.map m) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ m

theorem fracMap_smul [IsDomain M] (s : AmbientSemilinearAut K G M) (g : G)
    (x : FractionRing M) :
    s.fracMap (g • x) = g • s.fracMap x := by
  have h : (MulSemiringAction.toRingEquiv G M g).trans s.map =
      s.map.trans (MulSemiringAction.toRingEquiv G M g) :=
    RingEquiv.ext fun m => s.map_smul g m
  have hx := DFunLike.congr_fun (congrArg (IsFractionRing.ringEquivOfRingEquiv
    (K := FractionRing M) (L := FractionRing M)) h) x
  rwa [IsFractionRing.ringEquivOfRingEquiv_comp (FractionRing M) (FractionRing M) (FractionRing M),
    IsFractionRing.ringEquivOfRingEquiv_comp (FractionRing M) (FractionRing M)
      (FractionRing M)] at hx

theorem fracMap_algebraMap_const (s : AmbientSemilinearAut K G M) (c : K) :
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

end Transport

section Coeff

/-- **Restriction to the fixed field.** The restriction of an ambient semilinear automorphism
to the field fixed by `G`, as a ring equivalence. -/
def invMap [IsDomain M] (s : AmbientSemilinearAut K G M) :
    (FixedPoints.intermediateField G : IntermediateField K (FractionRing M)) ≃+*
      (FixedPoints.intermediateField G : IntermediateField K (FractionRing M)) where
  toFun x := ⟨s.fracMap (x : FractionRing M), fun g => by rw [← fracMap_smul, x.2 g]⟩
  invFun x := ⟨s.fracMap.symm (x : FractionRing M), fun g => by
    apply s.fracMap.injective
    rw [fracMap_smul, RingEquiv.apply_symm_apply, x.2 g]⟩
  left_inv x := Subtype.ext (s.fracMap.symm_apply_apply (x : FractionRing M))
  right_inv x := Subtype.ext (s.fracMap.apply_symm_apply (x : FractionRing M))
  map_mul' x y := Subtype.ext (map_mul s.fracMap (x : FractionRing M) y)
  map_add' x y := Subtype.ext (map_add s.fracMap (x : FractionRing M) y)

/-- **Coefficient action on the fixed field.** The semilinear automorphism of the field fixed
by `G` induced by an ambient semilinear automorphism. -/
def coeffAct [IsDomain M] (s : AmbientSemilinearAut K G M) :
    AlgebraicCurve.SemilinearAut K
      (FixedPoints.intermediateField G : IntermediateField K (FractionRing M)) :=
  ⟨(s.invMap, s.base), fun c => Subtype.ext (by
    change s.fracMap (algebraMap K (FractionRing M) c) =
      algebraMap K (FractionRing M) (s.base c)
    exact fracMap_algebraMap_const s c)⟩

theorem coeffAct_baseAut [IsDomain M] (s : AmbientSemilinearAut K G M) :
    AlgebraicCurve.SemilinearAut.baseAut (coeffAct s) = s.base := rfl

theorem coe_coeffAct_toRingAut [IsDomain M] (s : AmbientSemilinearAut K G M)
    (x : (FixedPoints.intermediateField G : IntermediateField K (FractionRing M))) :
    ((AlgebraicCurve.SemilinearAut.toRingAut (coeffAct s) x :
      (FixedPoints.intermediateField G : IntermediateField K (FractionRing M))) :
        FractionRing M) =
      s.fracMap (x : FractionRing M) := rfl

/-- **Coefficient action on the fixed field as a homomorphism.** The induced action on the
field fixed by `G`, as a group homomorphism. -/
def coeffActHom [IsDomain M] :
    AmbientSemilinearAut K G M →* AlgebraicCurve.SemilinearAut K
      (FixedPoints.intermediateField G : IntermediateField K (FractionRing M)) where
  toFun := coeffAct
  map_one' := Subtype.ext (Prod.ext (RingEquiv.ext fun x => Subtype.ext
    (DFunLike.congr_fun (IsFractionRing.ringEquivOfRingEquiv_refl (A := M)
      (K := FractionRing M)) (x : FractionRing M))) rfl)
  map_mul' s t := Subtype.ext (Prod.ext (RingEquiv.ext fun x => Subtype.ext
    (DFunLike.congr_fun (IsFractionRing.ringEquivOfRingEquiv_comp (FractionRing M)
      (FractionRing M) (FractionRing M) t.map s.map) (x : FractionRing M))) rfl)

@[simp] theorem coeffActHom_apply [IsDomain M] (s : AmbientSemilinearAut K G M) :
    coeffActHom s = coeffAct s := rfl

theorem coeffAct_comm_smul [IsDomain M] (s : AmbientSemilinearAut K G M) (g : G)
    (x : (FixedPoints.intermediateField G : IntermediateField K (FractionRing M))) :
    ((AlgebraicCurve.SemilinearAut.toRingAut (coeffAct s) x :
      (FixedPoints.intermediateField G : IntermediateField K (FractionRing M))) :
        FractionRing M) =
      s.fracMap (x : FractionRing M) ∧
    s.fracMap (g • (x : FractionRing M)) = g • s.fracMap (x : FractionRing M) :=
  ⟨rfl, fracMap_smul s g x⟩

theorem fracMap_comm_residualAct [IsDomain M] (s : AmbientSemilinearAut K G M)
    (N : Subgroup G) [N.Normal] (g : G)
    (x : (FixedPoints.intermediateField N : IntermediateField K (FractionRing M))) :
    s.fracMap ((residualAct K G M N g x :
      (FixedPoints.intermediateField N : IntermediateField K (FractionRing M))) :
        FractionRing M) =
      g • s.fracMap (x : FractionRing M) := by
  rw [coe_residualAct, fracMap_smul]

/-- **Restriction to the field fixed by a subgroup.** The restriction of an ambient semilinear
automorphism to the field fixed by `Γ`, as a ring equivalence. -/
def invMapOf [IsDomain M] (Γ : Subgroup G) (s : AmbientSemilinearAut K G M) :
    (FixedPoints.intermediateField Γ : IntermediateField K (FractionRing M)) ≃+*
      (FixedPoints.intermediateField Γ : IntermediateField K (FractionRing M)) where
  toFun x := ⟨s.fracMap (x : FractionRing M), fun g => by
    change (g : G) • s.fracMap (x : FractionRing M) = s.fracMap (x : FractionRing M)
    rw [← fracMap_smul]
    exact congrArg s.fracMap (x.2 g)⟩
  invFun x := ⟨s.fracMap.symm (x : FractionRing M), fun g => by
    change (g : G) • s.fracMap.symm (x : FractionRing M) = s.fracMap.symm (x : FractionRing M)
    apply s.fracMap.injective
    rw [fracMap_smul, RingEquiv.apply_symm_apply]
    exact x.2 g⟩
  left_inv x := Subtype.ext (s.fracMap.symm_apply_apply (x : FractionRing M))
  right_inv x := Subtype.ext (s.fracMap.apply_symm_apply (x : FractionRing M))
  map_mul' x y := Subtype.ext (map_mul s.fracMap (x : FractionRing M) y)
  map_add' x y := Subtype.ext (map_add s.fracMap (x : FractionRing M) y)

theorem coe_invMapOf [IsDomain M] (Γ : Subgroup G) (s : AmbientSemilinearAut K G M)
    (x : (FixedPoints.intermediateField Γ : IntermediateField K (FractionRing M))) :
    ((invMapOf Γ s x : (FixedPoints.intermediateField Γ : IntermediateField K (FractionRing M))) :
      FractionRing M) =
      s.fracMap (x : FractionRing M) := rfl

/-- **Coefficient action on the field fixed by a subgroup.** The semilinear automorphism of the
`Γ`-fixed field induced by an ambient semilinear automorphism. -/
def coeffActOf [IsDomain M] (Γ : Subgroup G) (s : AmbientSemilinearAut K G M) :
    AlgebraicCurve.SemilinearAut K
      (FixedPoints.intermediateField Γ : IntermediateField K (FractionRing M)) :=
  ⟨(invMapOf Γ s, s.base), fun c => Subtype.ext (by
    change s.fracMap (algebraMap K (FractionRing M) c) =
      algebraMap K (FractionRing M) (s.base c)
    exact fracMap_algebraMap_const s c)⟩

theorem coeffActOf_baseAut [IsDomain M] (Γ : Subgroup G) (s : AmbientSemilinearAut K G M) :
    AlgebraicCurve.SemilinearAut.baseAut (coeffActOf Γ s) = s.base := rfl

theorem coe_coeffActOf_toRingAut [IsDomain M] (Γ : Subgroup G) (s : AmbientSemilinearAut K G M)
    (x : (FixedPoints.intermediateField Γ : IntermediateField K (FractionRing M))) :
    ((AlgebraicCurve.SemilinearAut.toRingAut (coeffActOf Γ s) x :
      (FixedPoints.intermediateField Γ : IntermediateField K (FractionRing M))) :
        FractionRing M) =
      s.fracMap (x : FractionRing M) := rfl

/-- **Coefficient action on the field fixed by a subgroup as a homomorphism.** The induced
action on `Γ`-fixed fields, as a group homomorphism. -/
def coeffActOfHom [IsDomain M] (Γ : Subgroup G) :
    AmbientSemilinearAut K G M →* AlgebraicCurve.SemilinearAut K
      (FixedPoints.intermediateField Γ : IntermediateField K (FractionRing M)) where
  toFun := coeffActOf Γ
  map_one' := Subtype.ext (Prod.ext (RingEquiv.ext fun x => Subtype.ext
    (DFunLike.congr_fun (IsFractionRing.ringEquivOfRingEquiv_refl (A := M)
      (K := FractionRing M)) (x : FractionRing M))) rfl)
  map_mul' s t := Subtype.ext (Prod.ext (RingEquiv.ext fun x => Subtype.ext
    (DFunLike.congr_fun (IsFractionRing.ringEquivOfRingEquiv_comp (FractionRing M)
      (FractionRing M) (FractionRing M) t.map s.map) (x : FractionRing M))) rfl)

@[simp] theorem coeffActOfHom_apply [IsDomain M] (Γ : Subgroup G)
    (s : AmbientSemilinearAut K G M) :
    coeffActOfHom Γ s = coeffActOf Γ s := rfl

theorem coeffActOf_comm_residualAct [IsDomain M] (N : Subgroup G) [N.Normal]
    (s : AmbientSemilinearAut K G M) (g : G)
    (x : (FixedPoints.intermediateField N : IntermediateField K (FractionRing M))) :
    AlgebraicCurve.SemilinearAut.toRingAut (coeffActOf N s) (residualAct K G M N g x) =
      residualAct K G M N g (AlgebraicCurve.SemilinearAut.toRingAut (coeffActOf N s) x) :=
  Subtype.ext (by
    rw [coe_coeffActOf_toRingAut, coe_residualAct, coe_residualAct, coe_coeffActOf_toRingAut,
      fracMap_smul])

end Coeff

end AmbientSemilinearAut

section Normalizer

theorem smul_mem_fixedPoints_of_forall_mem [IsDomain M] (g : G) {Δ Δ' : Subgroup G}
    (h : ∀ d : G, d ∈ Δ' → g⁻¹ * d * g ∈ Δ) {x : FractionRing M}
    (hx : x ∈ (FixedPoints.intermediateField Δ : IntermediateField K (FractionRing M))) :
    g • x ∈ (FixedPoints.intermediateField Δ' : IntermediateField K (FractionRing M)) :=
  fun d => by
    change (d : G) • g • x = g • x
    rw [← mul_smul, show (d : G) * g = g * (g⁻¹ * d * g) from by group, mul_smul]
    congr 1
    exact hx ⟨g⁻¹ * d * g, h d d.2⟩

theorem smul_mem_fixedPoints_of_mem_normalizer [IsDomain M] (Δ : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (Δ : Set G)) {x : FractionRing M}
    (hx : x ∈ (FixedPoints.intermediateField Δ : IntermediateField K (FractionRing M))) :
    g • x ∈ (FixedPoints.intermediateField Δ : IntermediateField K (FractionRing M)) :=
  smul_mem_fixedPoints_of_forall_mem K G M g
    (fun d hd => (Subgroup.mem_normalizer_iff''.1 hg d).1 hd) hx

/-- **Conjugation transport as a ring equivalence.** Transport of the field fixed by `Δ` to the
field fixed by `Δ'` by the action of `g`, as a ring equivalence. It requires conjugation by
`g`, the map `d ↦ g * d * g⁻¹`, to carry `Δ` onto `Δ'`: `d ∈ Δ'` exactly when
`g⁻¹ * d * g ∈ Δ`. -/
def conjTransportRingEquiv [IsDomain M] (g : G) (Δ Δ' : Subgroup G)
    (h : ∀ d : G, d ∈ Δ' ↔ g⁻¹ * d * g ∈ Δ) :
    (FixedPoints.intermediateField Δ : IntermediateField K (FractionRing M)) ≃+*
      (FixedPoints.intermediateField Δ' : IntermediateField K (FractionRing M)) where
  toFun x := ⟨g • (x : FractionRing M),
    smul_mem_fixedPoints_of_forall_mem K G M g (fun d hd => (h d).1 hd) x.2⟩
  invFun y := ⟨g⁻¹ • (y : FractionRing M),
    smul_mem_fixedPoints_of_forall_mem K G M g⁻¹ (fun d hd => (h (g⁻¹⁻¹ * d * g⁻¹)).2 (by
      simpa only [inv_inv, mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left, inv_mul_cancel,
        mul_one] using hd)) y.2⟩
  left_inv x := Subtype.ext (inv_smul_smul g (x : FractionRing M))
  right_inv y := Subtype.ext (smul_inv_smul g (y : FractionRing M))
  map_mul' x y := Subtype.ext (smul_mul' g (x : FractionRing M) y)
  map_add' x y := Subtype.ext (smul_add g (x : FractionRing M) y)

theorem coe_conjTransportRingEquiv [IsDomain M] (g : G) (Δ Δ' : Subgroup G)
    (h : ∀ d : G, d ∈ Δ' ↔ g⁻¹ * d * g ∈ Δ)
    (x : (FixedPoints.intermediateField Δ : IntermediateField K (FractionRing M))) :
    ((conjTransportRingEquiv K G M g Δ Δ' h x :
      (FixedPoints.intermediateField Δ' : IntermediateField K (FractionRing M))) :
        FractionRing M) =
      g • (x : FractionRing M) := rfl

/-- **Conjugation transport.** Transport of the field fixed by `Δ` to the field fixed by `Δ'`
by the action of `g`, as a `K`-algebra equivalence. It requires conjugation by `g`, the map
`d ↦ g * d * g⁻¹`, to carry `Δ` onto `Δ'`: `d ∈ Δ'` exactly when `g⁻¹ * d * g ∈ Δ`. -/
def conjTransport [IsDomain M] (g : G) (Δ Δ' : Subgroup G)
    (h : ∀ d : G, d ∈ Δ' ↔ g⁻¹ * d * g ∈ Δ) :
    (FixedPoints.intermediateField Δ : IntermediateField K (FractionRing M)) ≃ₐ[K]
      (FixedPoints.intermediateField Δ' : IntermediateField K (FractionRing M)) :=
  AlgEquiv.ofRingEquiv (f := conjTransportRingEquiv K G M g Δ Δ' h) (fun c => Subtype.ext (by
    rw [coe_conjTransportRingEquiv]
    exact smul_algebraMap g c))

theorem coe_conjTransport [IsDomain M] (g : G) (Δ Δ' : Subgroup G)
    (h : ∀ d : G, d ∈ Δ' ↔ g⁻¹ * d * g ∈ Δ)
    (x : (FixedPoints.intermediateField Δ : IntermediateField K (FractionRing M))) :
    ((conjTransport K G M g Δ Δ' h x :
      (FixedPoints.intermediateField Δ' : IntermediateField K (FractionRing M))) :
        FractionRing M) =
      g • (x : FractionRing M) :=
  rfl

theorem coe_conjTransport_symm [IsDomain M] (g : G) (Δ Δ' : Subgroup G)
    (h : ∀ d : G, d ∈ Δ' ↔ g⁻¹ * d * g ∈ Δ)
    (y : (FixedPoints.intermediateField Δ' : IntermediateField K (FractionRing M))) :
    (((conjTransport K G M g Δ Δ' h).symm y :
      (FixedPoints.intermediateField Δ : IntermediateField K (FractionRing M))) :
        FractionRing M) =
      g⁻¹ • (y : FractionRing M) :=
  rfl

theorem mem_map_conj_iff (g : G) (Δ : Subgroup G) (d : G) :
    d ∈ Δ.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * d * g ∈ Δ := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem mem_iff_of_mem_normalizer (Δ : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (Δ : Set G)) (d : G) :
    d ∈ Δ ↔ g⁻¹ * d * g ∈ Δ :=
  Subgroup.mem_normalizer_iff''.1 hg d

/-- **Normalizer action.** The action of the normalizer of `Δ` on the `Δ`-fixed field, as
`K`-algebra equivalences. -/
def normalizerAct [IsDomain M] (Δ : Subgroup G) :
    ↥(Subgroup.normalizer (Δ : Set G)) →*
      ((FixedPoints.intermediateField Δ : IntermediateField K (FractionRing M)) ≃ₐ[K]
        (FixedPoints.intermediateField Δ : IntermediateField K (FractionRing M))) where
  toFun n := conjTransport K G M (n : G) Δ Δ (mem_iff_of_mem_normalizer G Δ n.2)
  map_one' := AlgEquiv.ext fun x => Subtype.ext (one_smul G (x : FractionRing M))
  map_mul' n n' :=
    AlgEquiv.ext fun x => Subtype.ext (mul_smul (n : G) (n' : G) (x : FractionRing M))

theorem coe_normalizerAct [IsDomain M] (Δ : Subgroup G)
    (n : ↥(Subgroup.normalizer (Δ : Set G)))
    (x : (FixedPoints.intermediateField Δ : IntermediateField K (FractionRing M))) :
    ((normalizerAct K G M Δ n x :
      (FixedPoints.intermediateField Δ : IntermediateField K (FractionRing M))) :
        FractionRing M) =
      (n : G) • (x : FractionRing M) :=
  rfl

theorem normalizerAct_eq_one_of_mem [IsDomain M] (Δ : Subgroup G)
    {n : ↥(Subgroup.normalizer (Δ : Set G))} (hn : (n : G) ∈ Δ) :
    normalizerAct K G M Δ n = 1 :=
  AlgEquiv.ext fun x => Subtype.ext (x.2 ⟨n, hn⟩)

theorem normalizerAct_eq_residualAct [IsDomain M] (N : Subgroup G) [N.Normal]
    (n : ↥(Subgroup.normalizer (N : Set G))) :
    normalizerAct K G M N n = residualAct K G M N (n : G) :=
  AlgEquiv.ext fun _ => Subtype.ext rfl

theorem coeffActOf_comm_conjTransport [IsDomain M] (s : AmbientSemilinearAut K G M) (g : G)
    (Δ Δ' : Subgroup G)
    (h : ∀ d : G, d ∈ Δ' ↔ g⁻¹ * d * g ∈ Δ)
    (x : (FixedPoints.intermediateField Δ : IntermediateField K (FractionRing M))) :
    AlgebraicCurve.SemilinearAut.toRingAut (AmbientSemilinearAut.coeffActOf Δ' s)
        (conjTransport K G M g Δ Δ' h x) =
      conjTransport K G M g Δ Δ' h
        (AlgebraicCurve.SemilinearAut.toRingAut (AmbientSemilinearAut.coeffActOf Δ s) x) :=
  Subtype.ext (by
    rw [AmbientSemilinearAut.coe_coeffActOf_toRingAut, coe_conjTransport, coe_conjTransport,
      AmbientSemilinearAut.coe_coeffActOf_toRingAut, AmbientSemilinearAut.fracMap_smul])

theorem coeffActOf_comm_normalizerAct [IsDomain M] (s : AmbientSemilinearAut K G M)
    (Δ : Subgroup G)
    (n : ↥(Subgroup.normalizer (Δ : Set G)))
    (x : (FixedPoints.intermediateField Δ : IntermediateField K (FractionRing M))) :
    AlgebraicCurve.SemilinearAut.toRingAut (AmbientSemilinearAut.coeffActOf Δ s)
        (normalizerAct K G M Δ n x) =
      normalizerAct K G M Δ n
        (AlgebraicCurve.SemilinearAut.toRingAut (AmbientSemilinearAut.coeffActOf Δ s) x) :=
  coeffActOf_comm_conjTransport K G M s (n : G) Δ Δ (mem_iff_of_mem_normalizer G Δ n.2) x

theorem coe_conjTransport_eq_of_le [IsDomain M] (g : G) {Δ₁ Δ₂ Δ₁' Δ₂' : Subgroup G}
    (h12 : Δ₂ ≤ Δ₁)
    (h₁ : ∀ d : G, d ∈ Δ₁' ↔ g⁻¹ * d * g ∈ Δ₁) (h₂ : ∀ d : G, d ∈ Δ₂' ↔ g⁻¹ * d * g ∈ Δ₂)
    (x : (FixedPoints.intermediateField Δ₁ : IntermediateField K (FractionRing M))) :
    ((conjTransport K G M g Δ₂ Δ₂' h₂ ⟨x, fun d => x.2 ⟨d, h12 d.2⟩⟩ :
        (FixedPoints.intermediateField Δ₂' : IntermediateField K (FractionRing M))) :
        FractionRing M) =
      ((conjTransport K G M g Δ₁ Δ₁' h₁ x :
        (FixedPoints.intermediateField Δ₁' : IntermediateField K (FractionRing M))) :
          FractionRing M) :=
  rfl

end Normalizer

end Generic

section MumfordLayer

variable (K : Type*) [Field K] (G : Type*) [Group G] (M : Type*) [CommRing M] [IsDomain M]
variable [Algebra K M]
variable [MulSemiringAction G M] [SMulCommClass G K M]

/-- **Mumford field.** The invariant field of the Mumford quotient layer: the field of
elements of the fraction ring of `M` fixed by `G`, that is, Mathlib's
`FixedPoints.intermediateField`. -/
abbrev mumfordField : IntermediateField K (FractionRing M) := FixedPoints.intermediateField G

variable {W : Type*} [MulAction G W] (𝒯 : SimpleGraph W) (w₀ : W)

variable {G} in
/-- **Type exchanger.** The element `g` exchanges the two vertex types: it adds one to the
type of every vertex. -/
def IsTypeExchanger (g : G) : Prop :=
  ∀ w : W, vertexType 𝒯 w₀ (g • w) = vertexType 𝒯 w₀ w + 1

/-- **Existence of a type exchanger.** There is an element of `G` exchanging the two vertex
types, that is, adding one to the type of every vertex. -/
def HasTypeExchanger : Prop := ∃ g : G, IsTypeExchanger 𝒯 w₀ g

variable {G 𝒯 w₀} in
/-- **Type exchangers are not type-preserving.** A type exchanger does not lie in the
type-preserving subgroup. -/
theorem IsTypeExchanger.notMem_typePreserving {g : G} (hg : IsTypeExchanger 𝒯 w₀ g) :
    g ∉ typePreserving G 𝒯 w₀ := fun hp => by
  have h := hg w₀
  rw [hp w₀, left_eq_add] at h
  exact one_ne_zero h

variable {G 𝒯 w₀} in
theorem HasTypeExchanger.exists_notMem_typePreserving (h : HasTypeExchanger G 𝒯 w₀) :
    ∃ g : G, g ∉ typePreserving G 𝒯 w₀ :=
  h.imp fun _ hg => hg.notMem_typePreserving

/-- **Mumford field of the type-preserving subgroup.** The field fixed by the type-preserving
subgroup, that is, Mathlib's `FixedPoints.intermediateField` of that subgroup. -/
abbrev mumfordFieldPlus : IntermediateField K (FractionRing M) :=
  FixedPoints.intermediateField (typePreserving G 𝒯 w₀)

theorem mumfordField_le_mumfordFieldPlus : mumfordField K G M ≤ mumfordFieldPlus K G M 𝒯 w₀ :=
  fun _ hx g => hx g

/-- **Exchanger action.** The residual action of `G` on the field fixed by the
type-preserving subgroup. -/
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
