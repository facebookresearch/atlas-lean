/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.Dual.Basis
public import MathlibExt.RepresentationTheory.AdmissibleRepresentation.Regular

/-!
# Duals of admissible representations

Let `F` be a field, `G` a group, `S` a commutative `F`-algebra with a family
`act : G → (S →ₐ[F] S)` of `F`-algebra maps, `ρ` an `F`-linear representation of `G` on `V` and
`H` a subgroup of `G`, with the ring of invariants `E = S^H` and the `E`-module
`D_S(V) = (S ⊗_F V)^H` of `MathlibExt.RepresentationTheory.AdmissibleRepresentation`. Following
J.-M. Fontaine, *Représentations p-adiques semi-stables*, Astérisque 223 (1994), Exposé III, we
compare the module `D_S(V*)` of the dual representation `ρ.dual` on `V* = Module.Dual F V` with the
dual `E`-module of `D_S(V)`:

* the `S`-bilinear pairing `S ⊗_F V* × S ⊗_F V → S`, `(a ⊗ φ, b ⊗ v) ↦ a b φ(v)`
  (`Representation.baseChangeDualPairing`), deduced by extension of scalars from Mathlib's
  `Module.Dual.baseChange`, identifies `S ⊗_F V*` with the dual of `S ⊗_F V` when `V` is
  finite-dimensional, being then Mathlib's isomorphism `IsBaseChange.toDualBaseChange`
  (`Representation.baseChangeDualPairing_bijective`);
* the pairing is equivariant for the diagonal actions of `G`
  (`Representation.baseChangeDualPairing_map_map`), so it pairs `D_S(V*)` and `D_S(V)` into `E`;
  this gives Fontaine's natural `E`-linear map `D_S(V*) → D_S(V)*` (*op. cit.*, §1.3.4 p. 122;
  `Representation.periodsDual`);
* for a finite-dimensional `V` admissible in the basis form (`Representation.HasFixedBasis`), the
  basis of `S ⊗_F V*` dual to an `S`-basis of `S ⊗_F V` of `H`-fixed vectors
  (`Representation.baseChangeDualBasis`) consists of `H`-fixed vectors, so `V*` is admissible in
  the basis form (`Representation.HasFixedBasis.dual`), and the natural map `D_S(V*) → D_S(V)*`
  is an isomorphism of `E`-modules (`Representation.HasFixedBasis.periodsDual_bijective`,
  `Representation.HasFixedBasis.periodsDualEquiv`).

The last item is the analogue, for the basis form of admissibility, of Fontaine's statement for
admissible representations (*op. cit.*, §1.5.2 p. 124); it needs no regularity of `S`, the family
`act` need not be an action, and `E` is only a commutative ring: the proofs work with bases of
`S ⊗_F V` rather than with dimensions. For a regular ring `S`
(`Representation.IsRegularPeriodRing`), admissibility is equivalent to its basis form, so the dual
of an admissible representation is admissible and `D_S(V*) → D_S(V)*` is an isomorphism
(Fontaine–Ouyang, Theorem 3.14 (2); Fontaine, *op. cit.*, Proposition 1.5.2 p. 124;
`Representation.IsRegularPeriodRing.isAdmissible_dual`,
`Representation.IsRegularPeriodRing.periodsDual_bijective`).

As in Fontaine's §1, no topology is involved, and the continuity of the actions is never assumed.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Representation

variable {F G S V : Type*} [Field F] [Group G] [CommRing S] [Algebra F S] [AddCommGroup V]
  [Module F V]

/-! ### The pairing between `S ⊗_F V*` and `S ⊗_F V` -/

variable (F S V) in
/-- **The pairing between `S ⊗_F V*` and `S ⊗_F V`**, the `S`-bilinear map with
`(a ⊗ φ, b ⊗ v) ↦ a b φ(v)`, where `φ(v) ∈ F` is mapped to `S`: the extension of scalars
`LinearMap.liftBaseChange` of the base change `Module.Dual.baseChange : V* → (S ⊗_F V)*` of linear
forms on `V`. -/
def baseChangeDualPairing : S ⊗[F] Module.Dual F V →ₗ[S] S ⊗[F] V →ₗ[S] S :=
  (Module.Dual.baseChange S).liftBaseChange S

/-- The pairing of `a ⊗ φ` and `b ⊗ v` is `a b φ(v)`. -/
@[simp]
theorem baseChangeDualPairing_tmul_tmul (a : S) (φ : Module.Dual F V) (b : S) (v : V) :
    baseChangeDualPairing F S V (a ⊗ₜ φ) (b ⊗ₜ v) = a * b * algebraMap F S (φ v) := by
  rw [baseChangeDualPairing, LinearMap.liftBaseChange_tmul, LinearMap.smul_apply,
    Module.Dual.baseChange_apply_tmul, smul_eq_mul, Algebra.smul_def,
    mul_comm (algebraMap F S (φ v)) b, mul_assoc]

/-- For finite-dimensional `V`, the pairing, viewed as an `S`-linear map `S ⊗_F V* → (S ⊗_F V)*`,
is Mathlib's isomorphism `IsBaseChange.toDualBaseChange` for the base change `S ⊗_F V` of `V`. -/
theorem baseChangeDualPairing_eq_toDualBaseChange [FiniteDimensional F V] :
    baseChangeDualPairing F S V =
      ((TensorProduct.isBaseChange F V S).toDualBaseChange :
        S ⊗[F] Module.Dual F V →ₗ[S] Module.Dual S (S ⊗[F] V)) := by
  refine TensorProduct.AlgebraTensorModule.ext fun a φ =>
    TensorProduct.AlgebraTensorModule.ext fun b v => ?_
  have h := IsBaseChange.toDualBaseChange_tmul (TensorProduct.isBaseChange F V S) a φ v
  rw [TensorProduct.mk_apply] at h
  have hb : b ⊗ₜ[F] v = b • ((1 : S) ⊗ₜ[F] v) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [baseChangeDualPairing_tmul_tmul, hb, LinearEquiv.coe_coe, map_smul, h, smul_eq_mul,
    mul_left_comm, mul_assoc]

/-- **Perfectness of the pairing for finite-dimensional `V`**: the `S`-linear map
`S ⊗_F V* → (S ⊗_F V)*`, `x ↦ ⟨x, ·⟩`, induced by the pairing is bijective. -/
theorem baseChangeDualPairing_bijective [FiniteDimensional F V] :
    Function.Bijective (baseChangeDualPairing F S V) := by
  rw [baseChangeDualPairing_eq_toDualBaseChange]
  exact LinearEquiv.bijective _

/-- **The pairing is equivariant**: for `g ∈ G`, pairing the images of `x ∈ S ⊗_F V*` and
`y ∈ S ⊗_F V` under the diagonal actions `s ⊗ φ ↦ act g s ⊗ ρ.dual g φ` and
`s ⊗ v ↦ act g s ⊗ ρ g v` gives `act g` of the pairing of `x` and `y`. -/
theorem baseChangeDualPairing_map_map (ρ : Representation F G V) (act : G → S →ₐ[F] S) (g : G)
    (x : S ⊗[F] Module.Dual F V) (y : S ⊗[F] V) :
    baseChangeDualPairing F S V (TensorProduct.map (act g).toLinearMap (ρ.dual g) x)
        (TensorProduct.map (act g).toLinearMap (ρ g) y) =
      act g (baseChangeDualPairing F S V x y) := by
  induction x using TensorProduct.inductionOn with
  | tmul a φ =>
    induction y using TensorProduct.inductionOn with
    | tmul b v =>
      rw [TensorProduct.map_tmul, TensorProduct.map_tmul, baseChangeDualPairing_tmul_tmul,
        baseChangeDualPairing_tmul_tmul, AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply,
        dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, inv_self_apply, map_mul,
        map_mul, AlgHom.commutes]
    | add y z hy hz => simp only [map_add, hy, hz]
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']

/-! ### Fontaine's natural map `D_S(V*) → D_S(V)*` -/

/-- The pairing of a vector of `D_S(V*)` and a vector of `D_S(V)` lies in `S^H`. -/
theorem baseChangeDualPairing_mem_fixedSubalgebra {ρ : Representation F G V}
    {act : G → S →ₐ[F] S} {H : Subgroup G} {x : S ⊗[F] Module.Dual F V}
    (hx : x ∈ ρ.dual.periods act H) {y : S ⊗[F] V} (hy : y ∈ ρ.periods act H) :
    baseChangeDualPairing F S V x y ∈ fixedSubalgebra S act H :=
  mem_fixedSubalgebra.2 fun g hg => by
    rw [← baseChangeDualPairing_map_map ρ act g, mem_periods.1 hx g hg, mem_periods.1 hy g hg]

/-- **Fontaine's natural map `D_S(V*) → D_S(V)*`** (Fontaine, Exposé III, §1.3.4 p. 122): the
`S^H`-linear map sending `x ∈ D_S(V*)` to the linear form `y ↦ ⟨x, y⟩` on `D_S(V)`, where
`⟨x, y⟩ ∈ S^H` is the pairing `Representation.baseChangeDualPairing` of `x` and `y`. -/
def periodsDual (ρ : Representation F G V) (act : G → S →ₐ[F] S) (H : Subgroup G) :
    ρ.dual.periods act H →ₗ[fixedSubalgebra S act H]
      Module.Dual (fixedSubalgebra S act H) (ρ.periods act H) :=
  LinearMap.mk₂ (fixedSubalgebra S act H)
    (fun x y => ⟨baseChangeDualPairing F S V x y,
      baseChangeDualPairing_mem_fixedSubalgebra x.2 y.2⟩)
    (fun x x' y => Subtype.ext (by simp))
    (fun c x y => Subtype.ext (by simp [Subalgebra.smul_def]))
    (fun x y y' => Subtype.ext (by simp))
    (fun c x y => Subtype.ext (by simp [Subalgebra.smul_def]))

/-- The value of `periodsDual ρ act H x` at `y` is the pairing of `x` and `y`. -/
@[simp]
theorem coe_periodsDual_apply (ρ : Representation F G V) (act : G → S →ₐ[F] S) (H : Subgroup G)
    (x : ρ.dual.periods act H) (y : ρ.periods act H) :
    (ρ.periodsDual act H x y : S) = baseChangeDualPairing F S V x y :=
  rfl

/-! ### Duals of representations admissible in the basis form -/

section FixedBasis

variable [FiniteDimensional F V] {ι : Type*} [Finite ι] [DecidableEq ι]

/-- **The basis dual to an `S`-basis `(bᵢ)` of `S ⊗_F V`** under the pairing
`Representation.baseChangeDualPairing`, for finite-dimensional `V`: the `S`-basis `(b'ᵢ)` of
`S ⊗_F V*` whose image in `(S ⊗_F V)*` is the dual basis of `(bᵢ)`, that is, `⟨b'ᵢ, bⱼ⟩ = δᵢⱼ`. -/
def baseChangeDualBasis (b : Module.Basis ι S (S ⊗[F] V)) :
    Module.Basis ι S (S ⊗[F] Module.Dual F V) :=
  b.dualBasis.map (TensorProduct.isBaseChange F V S).toDualBaseChange.symm

/-- The image of the vector `b'ᵢ` of `Representation.baseChangeDualBasis b` in `(S ⊗_F V)*` is the
`i`-th vector of the dual basis of `b`. -/
@[simp]
theorem baseChangeDualPairing_baseChangeDualBasis (b : Module.Basis ι S (S ⊗[F] V)) (i : ι) :
    baseChangeDualPairing F S V (baseChangeDualBasis b i) = b.dualBasis i := by
  rw [baseChangeDualBasis, Module.Basis.map_apply, baseChangeDualPairing_eq_toDualBaseChange,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

/-- **The basis dual to a basis of `H`-fixed vectors is fixed**: if `(bᵢ)` is an `S`-basis of
`S ⊗_F V` of vectors of `D_S(V)`, then the vectors of the dual basis
`Representation.baseChangeDualBasis b` of `S ⊗_F V*` lie in `D_S(V*)`. -/
theorem baseChangeDualBasis_mem_periods {ρ : Representation F G V} {act : G → S →ₐ[F] S}
    {H : Subgroup G} (b : Module.Basis ι S (S ⊗[F] V)) (hb : ∀ i, b i ∈ ρ.periods act H)
    (i : ι) : baseChangeDualBasis b i ∈ ρ.dual.periods act H := by
  refine mem_periods.2 fun g hg => (baseChangeDualPairing_bijective (F := F) (S := S)
    (V := V)).1 (b.ext fun j => ?_)
  conv_lhs => rw [← mem_periods.1 (hb j) g hg]
  rw [baseChangeDualPairing_map_map, baseChangeDualPairing_baseChangeDualBasis,
    Module.Basis.dualBasis_apply_self]
  split_ifs <;> simp

end FixedBasis

/-- **Duals preserve the basis form of admissibility** (the analogue of Fontaine, Exposé III,
§1.5.2 p. 124): if `V` is finite-dimensional and `S ⊗_F V` has an `S`-basis of `H`-fixed vectors,
then `S ⊗_F V*` has an `S`-basis of `H`-fixed vectors, for the dual representation `ρ.dual`. The
proof takes the basis dual to the given one, `Representation.baseChangeDualBasis`. -/
theorem HasFixedBasis.dual [FiniteDimensional F V] {ρ : Representation F G V}
    {act : G → S →ₐ[F] S} {H : Subgroup G} (h : ρ.HasFixedBasis act H) :
    ρ.dual.HasFixedBasis act H := by
  obtain ⟨d, b, hb⟩ := h
  exact ⟨d, baseChangeDualBasis b, baseChangeDualBasis_mem_periods b hb⟩

/-- **Fontaine's natural map `D_S(V*) → D_S(V)*` is bijective in the basis form of admissibility**
(the analogue of Fontaine, Exposé III, §1.5.2 p. 124): if `V` is finite-dimensional and
`S ⊗_F V` has an `S`-basis `(bᵢ)` of `H`-fixed vectors, then `Representation.periodsDual` is
bijective. The proof shows that it maps the `S^H`-basis of `D_S(V*)` formed by the basis dual to
`(bᵢ)` to the basis dual to the `S^H`-basis `(bᵢ)` of `D_S(V)`. -/
theorem HasFixedBasis.periodsDual_bijective [FiniteDimensional F V] {ρ : Representation F G V}
    {act : G → S →ₐ[F] S} {H : Subgroup G} (h : ρ.HasFixedBasis act H) :
    Function.Bijective (ρ.periodsDual act H) := by
  obtain ⟨d, b, hb⟩ := h
  let B := periodsBasis b hb
  let B' := periodsBasis (baseChangeDualBasis b) (baseChangeDualBasis_mem_periods b hb)
  have : ρ.periodsDual act H = (B'.equiv B.dualBasis (_root_.Equiv.refl (Fin d))).toLinearMap :=
    B'.ext fun i => B.ext fun j => Subtype.ext (by
      simp only [B, B', LinearEquiv.coe_coe, Module.Basis.equiv_apply, _root_.Equiv.refl_apply,
        Module.Basis.dualBasis_apply_self, coe_periodsDual_apply, coe_periodsBasis,
        baseChangeDualPairing_baseChangeDualBasis]
      split_ifs <;> rfl)
  rw [this]
  exact (B'.equiv B.dualBasis (_root_.Equiv.refl (Fin d))).bijective

/-- **Fontaine's isomorphism `D_S(V*) ≃ D_S(V)*`** in the basis form of admissibility: when `V`
is finite-dimensional and `S ⊗_F V` has an `S`-basis of `H`-fixed vectors, the natural map
`Representation.periodsDual`, as an `S^H`-linear equivalence. -/
def HasFixedBasis.periodsDualEquiv [FiniteDimensional F V] {ρ : Representation F G V}
    {act : G → S →ₐ[F] S} {H : Subgroup G} (h : ρ.HasFixedBasis act H) :
    ρ.dual.periods act H ≃ₗ[fixedSubalgebra S act H]
      Module.Dual (fixedSubalgebra S act H) (ρ.periods act H) :=
  LinearEquiv.ofBijective (ρ.periodsDual act H) h.periodsDual_bijective

/-- The isomorphism `periodsDualEquiv` applied to `x` is the natural map `periodsDual` applied to
`x`. -/
@[simp]
theorem HasFixedBasis.periodsDualEquiv_apply [FiniteDimensional F V] {ρ : Representation F G V}
    {act : G → S →ₐ[F] S} {H : Subgroup G} (h : ρ.HasFixedBasis act H)
    (x : ρ.dual.periods act H) : h.periodsDualEquiv x = ρ.periodsDual act H x :=
  rfl

/-! ### Regular rings -/

section Regular

variable [IsDomain S] {ρ : Representation F G V} {act : G →* (S →ₐ[F] S)} {H : Subgroup G}

/-- **Duals of admissible representations** (Fontaine–Ouyang, Theorem 3.14 (2); Fontaine,
Exposé III, Proposition 1.5.2 p. 124): for a regular ring `S`, if `V` is admissible, then so is
its dual `V*`, for the dual representation `ρ.dual`. -/
theorem IsRegularPeriodRing.isAdmissible_dual (hS : IsRegularPeriodRing act H)
    (h : ρ.IsAdmissible act H) : ρ.dual.IsAdmissible act H := by
  have := h.1
  exact ((hS.isAdmissible_iff_hasFixedBasis ρ).1 h).dual.isAdmissible

/-- **`D_S(V*) ≃ D_S(V)*` for admissible representations** (Fontaine–Ouyang, Theorem 3.14 (2);
Fontaine, Exposé III, Proposition 1.5.2 p. 124): for a regular ring `S` and an admissible `V`,
Fontaine's natural map `Representation.periodsDual` from `D_S(V*)` to the dual `S^H`-module of
`D_S(V)` is bijective. -/
theorem IsRegularPeriodRing.periodsDual_bijective (hS : IsRegularPeriodRing act H)
    (h : ρ.IsAdmissible act H) : Function.Bijective (ρ.periodsDual act H) := by
  have := h.1
  exact ((hS.isAdmissible_iff_hasFixedBasis ρ).1 h).periodsDual_bijective

end Regular

end Representation
