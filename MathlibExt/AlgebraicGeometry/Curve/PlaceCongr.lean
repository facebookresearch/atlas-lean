/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicCurve_RatFuncPlaces.lean`
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

public import MathlibExt.AlgebraicGeometry.Curve.ChartDichotomy
public import MathlibExt.AlgebraicGeometry.Curve.LPolynomial

/-!
# Transport of places along field isomorphisms

A ring isomorphism `e : F ≃+* F'` that commutes with the algebra maps from `K` sends each place of
`F/K` to a place of `F'/K`, whose valuation subring is the pullback along `e.symm`. This file
defines that transport, `AlgebraicCurve.Place.congrRingEquiv`, shows that it preserves orders
(`ord_congrRingEquiv`), residue fields (`congrResidueAlgEquiv`) and degrees
(`deg_congrRingEquiv`), and packages it as an equivalence `congrEquiv`.
-/

@[expose] public section

noncomputable section

namespace AlgebraicCurve

namespace Place

section Congr

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (e : F ≃+* F')

/-- The ring isomorphism from a valuation subring `V` of `F` onto its pullback along `e.symm`, a
valuation subring of `F'`, given by `e`. -/
def comapSymmRingEquiv (V : ValuationSubring F) :
    V ≃+* (V.comap (e.symm : F' →+* F)) where
  toFun x := ⟨e x, by
    rw [ValuationSubring.mem_comap]
    change e.symm (e x) ∈ V
    rw [e.symm_apply_apply]
    exact x.2⟩
  invFun y := ⟨e.symm y, y.2⟩
  left_inv x := by
    ext
    exact e.symm_apply_apply x
  right_inv y := by
    ext
    exact e.apply_symm_apply y
  map_mul' x y := by
    ext
    exact e.map_mul x y
  map_add' x y := by
    ext
    exact e.map_add x y

@[simp]
theorem coe_comapSymmRingEquiv_apply (V : ValuationSubring F) (x : V) :
    ((comapSymmRingEquiv e V x : (V.comap (e.symm : F' →+* F))) : F') = e x := rfl

variable (he : ∀ a : K, e (algebraMap K F a) = algebraMap K F' a)
include he

theorem symm_algebraMap_comm (a : K) : e.symm (algebraMap K F' a) = algebraMap K F a := by
  rw [← he a, e.symm_apply_apply]

/-- The transport of a place along a field isomorphism `e : F ≃+* F'` that commutes with the
algebra maps from `K`: its valuation subring is the pullback of that of `v` along `e.symm`, that is,
the image of `v.toValuationSubring` under `e`. -/
def congrRingEquiv (v : Place K F) : Place K F' where
  toValuationSubring := v.toValuationSubring.comap (e.symm : F' →+* F)
  algebraMap_mem' a := by
    rw [ValuationSubring.mem_comap]
    change e.symm (algebraMap K F' a) ∈ v.toValuationSubring
    rw [symm_algebraMap_comm e he a]
    exact v.algebraMap_mem' a
  ne_top' := fun h =>
    v.ne_top' (SetLike.ext fun x =>
      ⟨fun _ => ValuationSubring.mem_top x, fun _ => by
        have hx : e x ∈ v.toValuationSubring.comap (e.symm : F' →+* F) := by
          rw [h]
          exact ValuationSubring.mem_top _
        rw [ValuationSubring.mem_comap] at hx
        have : e.symm (e x) ∈ v.toValuationSubring := hx
        rwa [e.symm_apply_apply] at this⟩)
  isPrincipalIdealRing' :=
    IsPrincipalIdealRing.of_surjective
      (comapSymmRingEquiv e v.toValuationSubring : _ ≃+* _)
      (comapSymmRingEquiv e v.toValuationSubring).surjective

@[simp]
theorem congrRingEquiv_toValuationSubring (v : Place K F) :
    (congrRingEquiv e he v).toValuationSubring
      = v.toValuationSubring.comap (e.symm : F' →+* F) := rfl

theorem ord_congrRingEquiv (v : Place K F) (f : F) :
    (congrRingEquiv e he v).ord (e f) = v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  have hπ' : Irreducible (comapSymmRingEquiv e v.toValuationSubring π) :=
    (MulEquiv.irreducible_iff (comapSymmRingEquiv e v.toValuationSubring)).mpr hπ
  have hu' : IsUnit (comapSymmRingEquiv e v.toValuationSubring (u : v.toValuationSubring)) :=
    u.isUnit.map (comapSymmRingEquiv e v.toValuationSubring)
  have key : e f
      = ((hu'.unit : (v.toValuationSubring.comap (e.symm : F' →+* F))) : F')
        * (((comapSymmRingEquiv e v.toValuationSubring π :
            (v.toValuationSubring.comap (e.symm : F' →+* F))) : F') ^ (v.ord f)) := by
    rw [IsUnit.unit_spec, coe_comapSymmRingEquiv_apply, coe_comapSymmRingEquiv_apply,
      ← map_zpow₀, ← map_mul, ← hu]
  rw [key]
  exact (congrRingEquiv e he v).ord_unit_smul_zpow hu'.unit hπ' (v.ord f)

/-- The `K`-algebra isomorphism between the residue fields of `v` and of its transport
`congrRingEquiv e he v`, induced by `e`. -/
def congrResidueAlgEquiv (v : Place K F) :
    v.ResidueField ≃ₐ[K] (congrRingEquiv e he v).ResidueField :=
  AlgEquiv.ofRingEquiv
    (f := IsLocalRing.ResidueField.mapEquiv (comapSymmRingEquiv e v.toValuationSubring))
    (fun a => by
      have h3 : (comapSymmRingEquiv e v.toValuationSubring)
            (algebraMap K v.toValuationSubring a)
          = algebraMap K (congrRingEquiv e he v).toValuationSubring a := by
        ext
        rw [coe_comapSymmRingEquiv_apply, coe_algebraMap, coe_algebraMap]
        exact he a
      change IsLocalRing.residue _ (comapSymmRingEquiv e v.toValuationSubring
        (algebraMap K v.toValuationSubring a)) = _
      rw [h3]
      rfl)

theorem deg_congrRingEquiv (v : Place K F) : (congrRingEquiv e he v).deg = v.deg :=
  ((congrResidueAlgEquiv e he v).toLinearEquiv.finrank_eq).symm

/-- Transport along `e` as an equivalence between the places of `F` and those of `F'`; its inverse
is transport along `e.symm`. -/
def congrEquiv : Place K F ≃ Place K F' where
  toFun := congrRingEquiv e he
  invFun := congrRingEquiv e.symm (symm_algebraMap_comm e he)
  left_inv v := by
    ext1
    refine SetLike.ext fun x => ?_
    change e.symm (e.symm.symm x) ∈ v.toValuationSubring ↔ x ∈ v.toValuationSubring
    rw [RingEquiv.symm_symm, e.symm_apply_apply]
  right_inv v := by
    ext1
    refine SetLike.ext fun x => ?_
    change e.symm.symm (e.symm x) ∈ v.toValuationSubring ↔ x ∈ v.toValuationSubring
    rw [RingEquiv.symm_symm, e.apply_symm_apply]

@[simp]
theorem congrEquiv_apply (v : Place K F) : congrEquiv e he v = congrRingEquiv e he v := rfl

@[simp]
theorem congrEquiv_symm_apply (v : Place K F') :
    (congrEquiv e he).symm v = congrRingEquiv e.symm (symm_algebraMap_comm e he) v := rfl

end Congr

end Place

end AlgebraicCurve

end
