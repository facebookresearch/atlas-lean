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
Authors: the contributors to Deicyde/diophantine-z-q.
-/

module

public import Mathlib.Algebra.Algebra.Subalgebra.Operations
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Lift
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# Admissible representations

Let `F` be a field, `G` a group, `S` a commutative `F`-algebra on which `G` acts through a family
`act : G → (S →ₐ[F] S)` of `F`-algebra maps, and `ρ` an `F`-linear representation of `G` on `V`.
For a subgroup `H` of `G`, J.-M. Fontaine, *Représentations p-adiques semi-stables*,
Astérisque 223 (1994), Exposé III, §1.3.2 p. 121, considers

* the ring of invariants `E = S^H` (`Representation.fixedSubalgebra`), and
* the `E`-module `D_S(V) = (S ⊗_F V)^H` (`Representation.periods`), the invariants of the
  diagonal action `s ⊗ v ↦ act g s ⊗ ρ g v`;
* the **comparison map** `α_V : S ⊗_E D_S(V) → S ⊗_F V`, `s ⊗ x ↦ s • x`, the `S`-linear map
  deduced by extension of scalars from the inclusion `D_S(V) ⊆ S ⊗_F V`
  (`Representation.comparison`).

An intertwining map `f : V → W` induces the `E`-linear map `D_S(f) : D_S(V) → D_S(W)`, the
restriction of `S ⊗ f` (`Representation.periodsMap`); this makes `D_S` an additive functor, and
`α` is natural in `V` (`Representation.comparison_comp_baseChange_periodsMap`).

For a finite-dimensional `V` and an `(F, H)`-regular ring `S`, Fontaine shows that
`dim_E D_S(V) ≤ dim_F V`, and calls `V` admissible when `α_V` is an isomorphism, which happens
exactly when equality holds
(*op. cit.*, §1.4.2 p. 123 and §1.5.1 p. 124; see
`MathlibExt.RepresentationTheory.AdmissibleRepresentation.Regular`). We record two forms of
admissibility, without assuming regularity:

* the **dimension form**: `V` is finite-dimensional and `dim_{S^H} D_S(V) = dim_F V`
  (`Representation.IsAdmissible`), the form in which Fontaine uses admissibility for potential
  semistability (*op. cit.*, Exposé III, §1.8.5 pp. 134–135);
* the **basis form**: `S ⊗_F V` has a finite `S`-basis, indexed by `Fin d` for some `d`, of
  `H`-invariant vectors, that is, `S ⊗_F V` is a trivial `S`-representation of `H` of finite rank
  (`Representation.HasFixedBasis`). Such a basis is an `S^H`-basis of `D_S(V)`
  (`Representation.periodsBasis`), so it makes `α_V` an isomorphism
  (`Representation.HasFixedBasis.comparison_bijective`), and, for a nonzero `S` and a
  finite-dimensional `V`, the basis form implies the dimension form
  (`Representation.HasFixedBasis.isAdmissible`). Conversely, for a nonzero `S` and a
  finite-dimensional `V`, if `α_V` is an isomorphism and `D_S(V)` is free over `S^H`, then the
  basis form holds (`Representation.hasFixedBasis_of_comparison_bijective`). Neither implication
  holds without these hypotheses: over the zero ring every `V` has the empty fixed basis, but
  `V = F²` is not admissible in the dimension form; and for `S = F`, trivial `H` and an
  infinite-dimensional `V`, `α_V` is an isomorphism and `D_S(V) = V` is free, but `S ⊗_F V` has
  no finite basis.

Both forms are invariant under an equivariant isomorphism of `F`-algebras
(`Representation.isAdmissible_iff_of_algEquiv`, `Representation.hasFixedBasis_iff_of_algEquiv`),
which identifies the rings of invariants and the modules `D_S(V)`.

When the family `act` comes from an action of `G`, the ring `S^G` is Mathlib's
`FixedPoints.subalgebra` (`Representation.fixedSubalgebra_toAlgHom_top`) and the `F`-subspace
underlying `D_S(V)` is the space of invariants of the tensor product of representations
`S ⊗_F V` (`Representation.restrictScalars_periods`); the module `D_S(V)` adds the structure of
an `S^H`-module.

For a field `E` over `F`, a homomorphism `ρ : G →* GL_n(E)` is an `F`-linear representation of `G`
on `Eⁿ` (`Representation.ofGL`).

All the statements are about abstract groups acting on rings and modules: as in Fontaine's §1, no
topology is involved, and the continuity of the actions is never assumed.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Representation

variable {F G S S' V W U : Type*} [Field F] [Group G] [CommRing S] [Algebra F S] [CommRing S']
  [Algebra F S'] [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W] [AddCommGroup U]
  [Module F U]

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

/-- For an action of `G` on `S` by a `MulSemiringAction` commuting with `F`, the ring of invariants
`S^G` of the family `MulSemiringAction.toAlgHom F S` is `FixedPoints.subalgebra F S G`. -/
theorem fixedSubalgebra_toAlgHom_top [MulSemiringAction G S] [SMulCommClass G F S] :
    fixedSubalgebra S (MulSemiringAction.toAlgHom (M := G) F S) ⊤ =
      FixedPoints.subalgebra F S G := by
  ext s
  simp [mem_fixedSubalgebra, FixedPoints.mem_subalgebra]

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

/-- **`D_S(V)` as a space of invariants**: for an action `act : G →* (S →ₐ[F] S)`, the `F`-subspace
underlying `D_S(V)` is the space of invariants of `H` in the tensor product of the
representation `g ↦ act g` of `G` on `S` with `ρ`. -/
theorem restrictScalars_periods (ρ : Representation F G V) (act : G →* (S →ₐ[F] S))
    (H : Subgroup G) :
    (ρ.periods act H).restrictScalars F =
      invariants ((tprod (AlgHom.toEnd.comp act) ρ).comp H.subtype) := by
  ext x
  simp only [Submodule.restrictScalars_mem, mem_periods, mem_invariants, MonoidHom.coe_comp,
    Function.comp_apply, Subgroup.coe_subtype, tprod_apply, Subtype.forall]
  rfl

/-! ### Admissibility -/

/-- **`V` is admissible for `S` as a representation of `H`, in the dimension form** (Fontaine,
Exposé III, §1.5.1 p. 124 and §1.8.5 pp. 134–135): `V` is finite-dimensional over `F` and
`dim_{S^H} (S ⊗_F V)^H = dim_F V`. -/
def IsAdmissible (ρ : Representation F G V) (act : G → S →ₐ[F] S) (H : Subgroup G) : Prop :=
  FiniteDimensional F V ∧
    Module.finrank (fixedSubalgebra S act H) (ρ.periods act H) = Module.finrank F V

/-- **`V` is admissible for `S` as a representation of `H`, in the basis form**: `S ⊗_F V` has a
finite `S`-basis, indexed by `Fin d` for some `d`, of vectors fixed by the diagonal action of `H`,
that is, it is a trivial `S`-representation of `H` of finite rank. -/
def HasFixedBasis (ρ : Representation F G V) (act : G → S →ₐ[F] S) (H : Subgroup G) : Prop :=
  ∃ (d : ℕ) (b : Module.Basis (Fin d) S (S ⊗[F] V)), ∀ i, b i ∈ ρ.periods act H

section FixedBasis

variable {ρ : Representation F G V} {act : G → S →ₐ[F] S} {H : Subgroup G} {ι : Type*}
  [Finite ι]

/-- The coordinates of a vector of `D_S(V)` in an `S`-basis of `S ⊗_F V` of `H`-fixed vectors lie
in `S^H`. -/
private theorem repr_mem_fixedSubalgebra (b : Module.Basis ι S (S ⊗[F] V))
    (hb : ∀ i, b i ∈ ρ.periods act H) {x : S ⊗[F] V} (hx : x ∈ ρ.periods act H) (i : ι) :
    b.repr x i ∈ fixedSubalgebra S act H := by
  have := Fintype.ofFinite ι
  refine mem_fixedSubalgebra.2 fun g hg => ?_
  have h : x = ∑ j, act g (b.repr x j) • b j := by
    conv_lhs => rw [← mem_periods.1 hx g hg, ← b.sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul_tmul, mem_periods.1 (hb j) g hg]
  have := congrArg (fun y => b.repr y i) h
  simp only [b.repr_sum_self] at this
  exact this.symm

/-- **An `S`-basis of `S ⊗_F V` of `H`-fixed vectors, indexed by a finite type, is an
`S^H`-basis of `D_S(V)`**: every `x ∈ D_S(V)` is a combination of the basis vectors with
coefficients in `S^H`. -/
def periodsBasis (b : Module.Basis ι S (S ⊗[F] V)) (hb : ∀ i, b i ∈ ρ.periods act H) :
    Module.Basis ι (fixedSubalgebra S act H) (ρ.periods act H) :=
  Module.Basis.mk (v := fun i => ⟨b i, hb i⟩)
    (LinearIndependent.of_comp (ρ.periods act H).subtype
      (b.linearIndependent.restrict_scalars' (fixedSubalgebra S act H)))
    (by
      have := Fintype.ofFinite ι
      rintro ⟨x, hx⟩ -
      refine (Submodule.mem_span_range_iff_exists_fun _).2
        ⟨fun i => ⟨b.repr x i, repr_mem_fixedSubalgebra b hb hx i⟩, Subtype.ext ?_⟩
      simp only [Submodule.coe_sum, Submodule.coe_smul, Subalgebra.smul_def]
      exact b.sum_repr x)

/-- The vectors of `periodsBasis b hb` are those of `b`. -/
@[simp]
theorem coe_periodsBasis (b : Module.Basis ι S (S ⊗[F] V)) (hb : ∀ i, b i ∈ ρ.periods act H)
    (i : ι) : (periodsBasis b hb i : S ⊗[F] V) = b i := by
  simp [periodsBasis]

end FixedBasis

/-- **The basis form of admissibility implies the dimension form**, for a nonzero ring `S` and a
finite-dimensional `V`: an `S`-basis of `S ⊗_F V` of `H`-fixed vectors is an `S^H`-basis of
`D_S(V)`, so `dim_{S^H} D_S(V) = rk_S (S ⊗_F V) = dim_F V`. -/
theorem HasFixedBasis.isAdmissible [Nontrivial S] [FiniteDimensional F V]
    {ρ : Representation F G V} {act : G → S →ₐ[F] S} {H : Subgroup G}
    (h : ρ.HasFixedBasis act H) : ρ.IsAdmissible act H := by
  obtain ⟨d, b, hb⟩ := h
  refine ⟨inferInstance, ?_⟩
  rw [Module.finrank_eq_card_basis (periodsBasis b hb),
    ← Module.finrank_baseChange (R := S) (S := F) (M' := V), Module.finrank_eq_card_basis b]

/-! ### The comparison map -/

/-- **The comparison map `α_V : S ⊗_{S^H} D_S(V) → S ⊗_F V`**, `s ⊗ x ↦ s • x` (Fontaine,
Exposé III, §1.3.2 p. 121): the `S`-linear map deduced by extension of scalars from the inclusion
of `D_S(V)` in `S ⊗_F V`. -/
def comparison (ρ : Representation F G V) (act : G → S →ₐ[F] S) (H : Subgroup G) :
    S ⊗[fixedSubalgebra S act H] ρ.periods act H →ₗ[S] S ⊗[F] V :=
  (ρ.periods act H).subtype.liftBaseChange S

/-- `α_V (s ⊗ x) = s • x`. -/
@[simp]
theorem comparison_tmul (ρ : Representation F G V) (act : G → S →ₐ[F] S) (H : Subgroup G)
    (s : S) (x : ρ.periods act H) : ρ.comparison act H (s ⊗ₜ x) = s • (x : S ⊗[F] V) :=
  rfl

/-- The image of `α_V` is the `S`-submodule of `S ⊗_F V` spanned by `D_S(V)`. -/
theorem range_comparison (ρ : Representation F G V) (act : G → S →ₐ[F] S) (H : Subgroup G) :
    LinearMap.range (ρ.comparison act H) = Submodule.span S (ρ.periods act H : Set (S ⊗[F] V)) := by
  refine le_antisymm ?_ (Submodule.span_le.2 fun x hx => ⟨1 ⊗ₜ ⟨x, hx⟩, by simp⟩)
  rintro _ ⟨y, rfl⟩
  induction y using TensorProduct.inductionOn with
  | tmul s x => exact Submodule.smul_mem _ s (Submodule.subset_span x.2)
  | add y z hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz

/-- **The basis form of admissibility makes `α_V` an isomorphism**: `α_V` maps the `S`-basis
`1 ⊗ bᵢ` of `S ⊗_{S^H} D_S(V)` to the basis `(bᵢ)` of `S ⊗_F V`. -/
theorem HasFixedBasis.comparison_bijective {ρ : Representation F G V} {act : G → S →ₐ[F] S}
    {H : Subgroup G} (h : ρ.HasFixedBasis act H) : Function.Bijective (ρ.comparison act H) := by
  obtain ⟨d, b, hb⟩ := h
  let c := Algebra.TensorProduct.basis S (periodsBasis b hb)
  have : ρ.comparison act H = (c.equiv b (_root_.Equiv.refl (Fin d))).toLinearMap :=
    c.ext fun i => by
      rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply]
      simp [c, Algebra.TensorProduct.basis_apply]
  rw [this]
  exact (c.equiv b (_root_.Equiv.refl (Fin d))).bijective

/-- **An isomorphism `α_V` gives the basis form of admissibility**, when `S` is nontrivial, `V` is
finite-dimensional and `D_S(V)` is free over `S^H`: `α_V` maps the `S`-basis `1 ⊗ dᵢ` of
`S ⊗_{S^H} D_S(V)` given by an `S^H`-basis `(dᵢ)` of `D_S(V)` to an `S`-basis `(dᵢ)` of
`S ⊗_F V`. -/
theorem hasFixedBasis_of_comparison_bijective [Nontrivial S] [FiniteDimensional F V]
    {ρ : Representation F G V} {act : G → S →ₐ[F] S} {H : Subgroup G}
    [Module.Free (fixedSubalgebra S act H) (ρ.periods act H)]
    (h : Function.Bijective (ρ.comparison act H)) : ρ.HasFixedBasis act H := by
  let bE := Module.Free.chooseBasis (fixedSubalgebra S act H) (ρ.periods act H)
  let b := (Algebra.TensorProduct.basis S bE).map (LinearEquiv.ofBijective _ h)
  have : Finite (Module.Free.ChooseBasisIndex (fixedSubalgebra S act H) (ρ.periods act H)) :=
    Module.Finite.finite_basis b
  let := Fintype.ofFinite (Module.Free.ChooseBasisIndex (fixedSubalgebra S act H)
    (ρ.periods act H))
  refine ⟨_, b.reindex (Fintype.equivFin _), fun i => ?_⟩
  simp [b, Algebra.TensorProduct.basis_apply]

/-! ### Functoriality -/

section Functoriality

variable {ρ : Representation F G V} {σ : Representation F G W} {τ : Representation F G U}

/-- For an intertwining map `f : V → W`, the map `S ⊗ f : S ⊗_F V → S ⊗_F W` commutes with the
diagonal actions. -/
theorem map_baseChange_comm (f : ρ.IntertwiningMap σ) (act : G → S →ₐ[F] S) (g : G)
    (x : S ⊗[F] V) :
    TensorProduct.map (act g).toLinearMap (σ g) (f.toLinearMap.baseChange S x) =
      f.toLinearMap.baseChange S (TensorProduct.map (act g).toLinearMap (ρ g) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s v => simp [f.isIntertwining]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **The functor `D_S` on morphisms**: an intertwining map `f : V → W` induces the
`S^H`-linear map `D_S(f) : D_S(V) → D_S(W)`, the restriction of `S ⊗ f`. -/
def periodsMap (act : G → S →ₐ[F] S) (H : Subgroup G) (f : ρ.IntertwiningMap σ) :
    ρ.periods act H →ₗ[fixedSubalgebra S act H] σ.periods act H :=
  ((f.toLinearMap.baseChange S).restrictScalars (fixedSubalgebra S act H)).restrict
    fun x hx => mem_periods.2 fun g hg => by
      rw [LinearMap.restrictScalars_apply, map_baseChange_comm, mem_periods.1 hx g hg]

variable {act : G → S →ₐ[F] S} {H : Subgroup G}

/-- `D_S(f)` is the restriction of `S ⊗ f`. -/
@[simp]
theorem coe_periodsMap (f : ρ.IntertwiningMap σ) (x : ρ.periods act H) :
    (periodsMap act H f x : S ⊗[F] W) = f.toLinearMap.baseChange S x :=
  rfl

/-- `D_S` maps the identity to the identity. -/
@[simp]
theorem periodsMap_id : periodsMap act H (IntertwiningMap.id ρ) = LinearMap.id := by
  ext x
  simp [IntertwiningMap.toLinearMap_id]

/-- `D_S` preserves composition. -/
theorem periodsMap_comp (f : σ.IntertwiningMap τ) (f' : ρ.IntertwiningMap σ) :
    periodsMap act H (f.comp f') = (periodsMap act H f).comp (periodsMap act H f') := by
  ext x
  simp [IntertwiningMap.comp_toLinearMap, LinearMap.baseChange_comp]

/-- `D_S` maps the zero map to the zero map. -/
@[simp]
theorem periodsMap_zero : periodsMap act H (0 : ρ.IntertwiningMap σ) = 0 := by
  ext x
  simp

/-- `D_S` is additive. -/
theorem periodsMap_add (f f' : ρ.IntertwiningMap σ) :
    periodsMap act H (f + f') = periodsMap act H f + periodsMap act H f' := by
  ext x
  simp [LinearMap.baseChange_add]

/-- **Naturality of `α`**: for an intertwining map `f : V → W`,
`α_W ∘ (S ⊗ D_S(f)) = (S ⊗ f) ∘ α_V`. -/
theorem comparison_comp_baseChange_periodsMap (f : ρ.IntertwiningMap σ) :
    σ.comparison act H ∘ₗ (periodsMap act H f).baseChange S =
      f.toLinearMap.baseChange S ∘ₗ ρ.comparison act H := by
  ext x
  simp

end Functoriality

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
