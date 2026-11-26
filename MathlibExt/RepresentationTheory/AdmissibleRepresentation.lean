/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from `ZInQKernel/Contrib/OneProof/BergerBst.lean`,
`ZInQKernel/Contrib/OneProof/PanBergerPst.lean`, `ZInQKernel/Contrib/OneProof/PstTransport.lean`
and `ZInQKernel/Contrib/OneProof/PanBergerFix.lean`
(https://github.com/Deicyde/diophantine-z-q), compared with the source files at commit
`e9956cda4174c060ff85f5a6ddc7e4003e63fdd3`.
Copyright 2026 the contributors to Deicyde/diophantine-z-q.
Licensed under the Apache License, Version 2.0.
-/

module

public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# Admissible representations

Let `F` be a field, `G` a group, `S` a commutative `F`-algebra on which `G` acts through a family
`act : G → (S →ₐ[F] S)` of `F`-algebra maps, and `ρ` an `F`-linear representation of `G` on `V`.
For a subgroup `H` of `G`, J.-M. Fontaine, *Le corps des périodes p-adiques*, Astérisque 223 (1994),
Exposé III, §1.5.1 p. 124, considers

* the ring of invariants `E = S^H` (`Representation.fixedSubalgebra`), and
* the `E`-module `D_S(V) = (S ⊗_F V)^H` (`Representation.periods`), the invariants of the
  diagonal action `s ⊗ v ↦ act g s ⊗ ρ g v`;

for a `(F, H)`-regular ring `S` he shows that `dim_E D_S(V) ≤ dim_F V`, and calls `V` admissible
when equality holds. We record two forms of admissibility, without assuming regularity:

* the **dimension form**: `V` is finite-dimensional and `dim_{S^H} D_S(V) = dim_F V`
  (`Representation.IsAdmissible`), the form in which Fontaine uses admissibility for potential
  semistability (*op. cit.*, Exposé III, §1.8.5 pp. 134–135);
* the **basis form**: `S ⊗_F V` has an `S`-basis of `H`-invariant vectors, that is, `S ⊗_F V` is a
  trivial `S`-representation of `H` (`Representation.HasFixedBasis`); it implies the dimension
  form (`Representation.HasFixedBasis.isAdmissible`), and the converse holds for regular rings.

Both forms are invariant under an equivariant isomorphism of `F`-algebras
(`Representation.isAdmissible_iff_of_algEquiv`, `Representation.hasFixedBasis_iff_of_algEquiv`),
which identifies the rings of invariants and the modules `D_S(V)`.

For a field `E` over `F`, a homomorphism `ρ : G →* GL_n(E)` is an `F`-linear representation of `G`
on `Eⁿ` (`Representation.ofGL`).
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Representation

variable {F G S S' V : Type*} [Field F] [Group G] [CommRing S] [Algebra F S] [CommRing S']
  [Algebra F S'] [AddCommGroup V] [Module F V]

/-! ### The ring of invariants and the module `D_S(V)` -/

variable (S) in
/-- **The ring of invariants `S^H`** of a family `act` of `F`-algebra maps `S → S` indexed by `G`,
for a subgroup `H` of `G`: the `F`-subalgebra of the `s ∈ S` with `act g s = s` for every
`g ∈ H`. -/
def fixedSubalgebra (act : G → S →ₐ[F] S) (H : Subgroup G) : Subalgebra F S where
  carrier := {s | ∀ g ∈ H, act g s = s}
  mul_mem' {a b} ha hb g hg := by
    rw [map_mul, ha g hg, hb g hg]
  add_mem' {a b} ha hb g hg := by
    rw [map_add, ha g hg, hb g hg]
  algebraMap_mem' c g _ := (act g).commutes c

/-- `s ∈ S^H` if and only if `act g s = s` for every `g ∈ H`. -/
theorem mem_fixedSubalgebra {act : G → S →ₐ[F] S} {H : Subgroup G} {s : S} :
    s ∈ fixedSubalgebra S act H ↔ ∀ g ∈ H, act g s = s :=
  Iff.rfl

/-- The diagonal action `s ⊗ v ↦ act g s ⊗ ρ g v` of `g ∈ G` on `S ⊗_F V` is semilinear over the
action of `g` on `S`. -/
theorem map_smul_tmul (ρ : Representation F G V) (act : G → S →ₐ[F] S) (g : G) (a : S)
    (x : S ⊗[F] V) :
    TensorProduct.map (act g).toLinearMap (ρ g) (a • x) =
      act g a • TensorProduct.map (act g).toLinearMap (ρ g) x := by
  induction x using TensorProduct.inductionOn with
  | tmul b v =>
    rw [TensorProduct.smul_tmul', TensorProduct.map_tmul, TensorProduct.map_tmul,
      TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, AlgHom.toLinearMap_apply,
      AlgHom.toLinearMap_apply, map_mul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- **Fontaine's module `D_S(V) = (S ⊗_F V)^H`**: the elements of `S ⊗_F V` fixed by the
diagonal action `s ⊗ v ↦ act g s ⊗ ρ g v` of every `g ∈ H`, a module over `S^H`. -/
def periods (ρ : Representation F G V) (act : G → S →ₐ[F] S) (H : Subgroup G) :
    Submodule (fixedSubalgebra S act H) (S ⊗[F] V) where
  carrier := {x | ∀ g ∈ H, TensorProduct.map (act g).toLinearMap (ρ g) x = x}
  zero_mem' g _ := map_zero _
  add_mem' {x y} hx hy g hg := by
    rw [map_add, hx g hg, hy g hg]
  smul_mem' c x hx g hg := by
    rw [Subalgebra.smul_def, map_smul_tmul, mem_fixedSubalgebra.1 c.2 g hg, hx g hg]

/-- `x ∈ D_S(V)` if and only if `x` is fixed by the diagonal action of every `g ∈ H`. -/
theorem mem_periods {ρ : Representation F G V} {act : G → S →ₐ[F] S} {H : Subgroup G}
    {x : S ⊗[F] V} :
    x ∈ ρ.periods act H ↔ ∀ g ∈ H, TensorProduct.map (act g).toLinearMap (ρ g) x = x :=
  Iff.rfl

/-! ### Admissibility -/

/-- **`V` is admissible for `S` as a representation of `H`, in the dimension form** (Fontaine,
Exposé III, §1.5.1 p. 124 and §1.8.5 pp. 134–135): `V` is finite-dimensional over `F` and
`dim_{S^H} (S ⊗_F V)^H = dim_F V`. -/
def IsAdmissible (ρ : Representation F G V) (act : G → S →ₐ[F] S) (H : Subgroup G) : Prop :=
  FiniteDimensional F V ∧
    Module.finrank (fixedSubalgebra S act H) (ρ.periods act H) = Module.finrank F V

/-- **`V` is admissible for `S` as a representation of `H`, in the basis form**: `S ⊗_F V` has an
`S`-basis of vectors fixed by the diagonal action of `H`, that is, it is a trivial
`S`-representation of `H`. -/
def HasFixedBasis (ρ : Representation F G V) (act : G → S →ₐ[F] S) (H : Subgroup G) : Prop :=
  ∃ (d : ℕ) (b : Module.Basis (Fin d) S (S ⊗[F] V)), ∀ i, b i ∈ ρ.periods act H

/-- The coordinates of a vector of `D_S(V)` in an `S`-basis of `S ⊗_F V` of `H`-fixed vectors lie
in `S^H`. -/
private theorem repr_mem_fixedSubalgebra {ρ : Representation F G V} {act : G → S →ₐ[F] S}
    {H : Subgroup G} {d : ℕ} (b : Module.Basis (Fin d) S (S ⊗[F] V))
    (hb : ∀ i, b i ∈ ρ.periods act H) {x : S ⊗[F] V} (hx : x ∈ ρ.periods act H) (i : Fin d) :
    b.repr x i ∈ fixedSubalgebra S act H := by
  refine mem_fixedSubalgebra.2 fun g hg => ?_
  have h : x = ∑ j, act g (b.repr x j) • b j := by
    conv_lhs => rw [← mem_periods.1 hx g hg, ← b.sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul_tmul, mem_periods.1 (hb j) g hg]
  have := congrArg (fun y => b.repr y i) h
  simp only [b.repr_sum_self] at this
  exact this.symm

/-- **The basis form of admissibility implies the dimension form**: an `S`-basis of `S ⊗_F V` of
`H`-fixed vectors is an `S^H`-basis of `D_S(V)`, so
`dim_{S^H} D_S(V) = rk_S (S ⊗_F V) = dim_F V`. -/
theorem HasFixedBasis.isAdmissible [Nontrivial S] [FiniteDimensional F V]
    {ρ : Representation F G V} {act : G → S →ₐ[F] S} {H : Subgroup G}
    (h : ρ.HasFixedBasis act H) : ρ.IsAdmissible act H := by
  obtain ⟨d, b, hb⟩ := h
  let v : Fin d → ρ.periods act H := fun i => ⟨b i, hb i⟩
  have hli : LinearIndependent (fixedSubalgebra S act H) v :=
    LinearIndependent.of_comp (ρ.periods act H).subtype
      (b.linearIndependent.restrict_scalars' (fixedSubalgebra S act H))
  have hsp : ⊤ ≤ Submodule.span (fixedSubalgebra S act H) (Set.range v) := by
    rintro ⟨x, hx⟩ -
    refine (Submodule.mem_span_range_iff_exists_fun _).2
      ⟨fun i => ⟨b.repr x i, repr_mem_fixedSubalgebra b hb hx i⟩, Subtype.ext ?_⟩
    simp only [Submodule.coe_sum, Submodule.coe_smul, Subalgebra.smul_def, v]
    exact b.sum_repr x
  refine ⟨inferInstance, ?_⟩
  rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp),
    ← Module.finrank_baseChange (R := S) (S := F) (M' := V), Module.finrank_eq_card_basis b]

/-! ### Invariance under equivariant isomorphisms -/

/-- `e ⊗ id : S ⊗_F V ≃ S' ⊗_F V` is semilinear over `e`. -/
private theorem rTensor_smul (e : S ≃ₐ[F] S') (a : S) (x : S ⊗[F] V) :
    e.toLinearEquiv.rTensor V (a • x) = e a • e.toLinearEquiv.rTensor V x := by
  induction x using TensorProduct.inductionOn with
  | tmul s v =>
    rw [TensorProduct.smul_tmul', LinearEquiv.rTensor_tmul, LinearEquiv.rTensor_tmul,
      TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, AlgEquiv.toLinearEquiv_apply,
      AlgEquiv.toLinearEquiv_apply, map_mul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- `e ⊗ id : S ⊗_F V ≃ S' ⊗_F V` intertwines the diagonal actions when `e` intertwines `act` and
`act'`. -/
private theorem map_rTensor (ρ : Representation F G V) {act : G → S →ₐ[F] S}
    {act' : G → S' →ₐ[F] S'} (e : S ≃ₐ[F] S') (he : ∀ g s, e (act g s) = act' g (e s)) (g : G)
    (x : S ⊗[F] V) :
    TensorProduct.map (act' g).toLinearMap (ρ g) (e.toLinearEquiv.rTensor V x) =
      e.toLinearEquiv.rTensor V (TensorProduct.map (act g).toLinearMap (ρ g) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s v =>
    rw [LinearEquiv.rTensor_tmul, TensorProduct.map_tmul, TensorProduct.map_tmul,
      LinearEquiv.rTensor_tmul, AlgEquiv.toLinearEquiv_apply, AlgEquiv.toLinearEquiv_apply,
      AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, he]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- `e ⊗ id : S ⊗_F V ≃ S' ⊗_F V` maps `D_S(V)` onto `D_{S'}(V)` when `e` intertwines `act` and
`act'`. -/
private theorem rTensor_mem_periods_iff (ρ : Representation F G V) {act : G → S →ₐ[F] S}
    {act' : G → S' →ₐ[F] S'} (e : S ≃ₐ[F] S') (he : ∀ g s, e (act g s) = act' g (e s))
    (H : Subgroup G) (x : S ⊗[F] V) :
    e.toLinearEquiv.rTensor V x ∈ ρ.periods act' H ↔ x ∈ ρ.periods act H := by
  simp only [mem_periods, map_rTensor ρ e he, EmbeddingLike.apply_eq_iff_eq]

/-- An isomorphism of `F`-algebras `e : S ≃ S'` intertwining `act` and `act'` induces a bijection
`S^H ≃ S'^H`. -/
private def fixedSubalgebraEquiv {act : G → S →ₐ[F] S} {act' : G → S' →ₐ[F] S'}
    (e : S ≃ₐ[F] S') (he : ∀ g s, e (act g s) = act' g (e s)) (H : Subgroup G) :
    fixedSubalgebra S act H ≃ fixedSubalgebra S' act' H where
  toFun c := ⟨e c, mem_fixedSubalgebra.2 fun g hg => by
    rw [← he, mem_fixedSubalgebra.1 c.2 g hg]⟩
  invFun c := ⟨e.symm c, mem_fixedSubalgebra.2 fun g hg => e.injective (by
    rw [he, e.apply_symm_apply, mem_fixedSubalgebra.1 c.2 g hg])⟩
  left_inv c := Subtype.ext (e.symm_apply_apply c)
  right_inv c := Subtype.ext (e.apply_symm_apply c)

/-- An isomorphism of `F`-algebras `e : S ≃ S'` intertwining `act` and `act'` induces an additive
isomorphism `D_S(V) ≃ D_{S'}(V)`, the restriction of `e ⊗ id`. -/
private def periodsAddEquiv (ρ : Representation F G V) {act : G → S →ₐ[F] S}
    {act' : G → S' →ₐ[F] S'} (e : S ≃ₐ[F] S') (he : ∀ g s, e (act g s) = act' g (e s))
    (H : Subgroup G) : ρ.periods act H ≃+ ρ.periods act' H where
  toFun x := ⟨e.toLinearEquiv.rTensor V x, (rTensor_mem_periods_iff ρ e he H x).2 x.2⟩
  invFun y := ⟨(e.toLinearEquiv.rTensor V).symm y, (rTensor_mem_periods_iff ρ e he H _).1 (by
    rw [LinearEquiv.apply_symm_apply]
    exact y.2)⟩
  left_inv x := Subtype.ext ((e.toLinearEquiv.rTensor V).symm_apply_apply x)
  right_inv y := Subtype.ext ((e.toLinearEquiv.rTensor V).apply_symm_apply y)
  map_add' x y := Subtype.ext (map_add (e.toLinearEquiv.rTensor V) (x : S ⊗[F] V) y)

/-- An isomorphism of `F`-algebras `e : S ≃ S'` intertwining `act` and `act'` preserves
`dim_{S^H} D_S(V)`. -/
private theorem finrank_periods_eq (ρ : Representation F G V) {act : G → S →ₐ[F] S}
    {act' : G → S' →ₐ[F] S'} (e : S ≃ₐ[F] S') (he : ∀ g s, e (act g s) = act' g (e s))
    (H : Subgroup G) :
    Module.finrank (fixedSubalgebra S act H) (ρ.periods act H) =
      Module.finrank (fixedSubalgebra S' act' H) (ρ.periods act' H) := by
  have h := lift_rank_eq_of_equiv_equiv (fixedSubalgebraEquiv e he H) (periodsAddEquiv ρ e he H)
    (fixedSubalgebraEquiv e he H).bijective fun r x =>
      Subtype.ext (rTensor_smul e (r : S) (x : S ⊗[F] V))
  simpa only [Module.finrank, Cardinal.toNat_lift] using congrArg Cardinal.toNat h

/-- An isomorphism of `F`-algebras `e : S ≃ S'` intertwining `act` and `act'` carries an `S`-basis
of `S ⊗_F V` of `H`-fixed vectors to an `S'`-basis of `S' ⊗_F V` of `H`-fixed vectors. -/
private theorem HasFixedBasis.of_algEquiv {ρ : Representation F G V} {act : G → S →ₐ[F] S}
    {act' : G → S' →ₐ[F] S'} (e : S ≃ₐ[F] S') (he : ∀ g s, e (act g s) = act' g (e s))
    {H : Subgroup G} (h : ρ.HasFixedBasis act H) : ρ.HasFixedBasis act' H := by
  obtain ⟨d, b, hb⟩ := h
  have hT : ∀ c : Fin d → S, e.toLinearEquiv.rTensor V (∑ i, c i • b i) =
      ∑ i, e (c i) • e.toLinearEquiv.rTensor V (b i) := fun c => by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => rTensor_smul e (c i) (b i)
  have hli : LinearIndependent S' fun i => e.toLinearEquiv.rTensor V (b i) := by
    refine Fintype.linearIndependent_iff.2 fun c hc i => ?_
    have h0 : ∑ i, e.symm (c i) • b i = 0 := (e.toLinearEquiv.rTensor V).injective (by
      rw [hT, map_zero]
      simpa only [AlgEquiv.apply_symm_apply] using hc)
    exact EmbeddingLike.map_eq_zero_iff.1
      (Fintype.linearIndependent_iff.1 b.linearIndependent _ h0 i)
  have hsp : ⊤ ≤ Submodule.span S' (Set.range fun i => e.toLinearEquiv.rTensor V (b i)) := by
    intro y _
    refine (Submodule.mem_span_range_iff_exists_fun _).2
      ⟨fun i => e (b.repr ((e.toLinearEquiv.rTensor V).symm y) i), ?_⟩
    rw [← hT, b.sum_repr, LinearEquiv.apply_symm_apply]
  refine ⟨d, Module.Basis.mk hli hsp, fun i => ?_⟩
  rw [Module.Basis.mk_apply, rTensor_mem_periods_iff ρ e he]
  exact hb i

/-- **Transport of admissibility, dimension form**: an isomorphism of `F`-algebras `e : S ≃ S'`
intertwining the families `act` and `act'` identifies `S^H` with `S'^H` and `D_S(V)` with
`D_{S'}(V)`, so `V` is admissible for `S` if and only if it is admissible for `S'`. -/
theorem isAdmissible_iff_of_algEquiv (ρ : Representation F G V) {act : G → S →ₐ[F] S}
    {act' : G → S' →ₐ[F] S'} (e : S ≃ₐ[F] S') (he : ∀ g s, e (act g s) = act' g (e s))
    (H : Subgroup G) : ρ.IsAdmissible act H ↔ ρ.IsAdmissible act' H := by
  rw [IsAdmissible, IsAdmissible, finrank_periods_eq ρ e he H]

/-- **Transport of admissibility, basis form**: an isomorphism of `F`-algebras `e : S ≃ S'`
intertwining the families `act` and `act'` carries `S`-bases of `S ⊗_F V` of `H`-fixed vectors to
`S'`-bases of `S' ⊗_F V` of `H`-fixed vectors. -/
theorem hasFixedBasis_iff_of_algEquiv (ρ : Representation F G V) {act : G → S →ₐ[F] S}
    {act' : G → S' →ₐ[F] S'} (e : S ≃ₐ[F] S') (he : ∀ g s, e (act g s) = act' g (e s))
    (H : Subgroup G) : ρ.HasFixedBasis act H ↔ ρ.HasFixedBasis act' H := by
  refine ⟨HasFixedBasis.of_algEquiv e he, HasFixedBasis.of_algEquiv e.symm fun g s => ?_⟩
  rw [AlgEquiv.symm_apply_eq, he, AlgEquiv.apply_symm_apply]

/-! ### Matrix representations -/

variable (F) in
/-- **The representation of `G` on `Eⁿ` defined by `ρ : G →* GL_n(E)`**, for an `F`-algebra `E`:
`g` acts by the matrix `ρ g`, viewed as an `F`-linear map. -/
def ofGL {E : Type*} [CommRing E] [Algebra F E] {n : ℕ} (ρ : G →* GL (Fin n) E) :
    Representation F G (Fin n → E) where
  toFun g := (Matrix.mulVecLin (ρ g : Matrix (Fin n) (Fin n) E)).restrictScalars F
  map_one' := by
    ext v
    simp
  map_mul' g h := by
    ext v
    simp

/-- `ofGL F ρ g` multiplies a vector by the matrix `ρ g`. -/
@[simp]
theorem ofGL_apply {E : Type*} [CommRing E] [Algebra F E] {n : ℕ} (ρ : G →* GL (Fin n) E) (g : G)
    (v : Fin n → E) : ofGL F ρ g v = (ρ g : Matrix (Fin n) (Fin n) E).mulVec v :=
  rfl

end Representation
