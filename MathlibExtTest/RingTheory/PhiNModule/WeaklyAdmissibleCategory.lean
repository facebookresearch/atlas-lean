/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RingTheory.PhiNModule.WeaklyAdmissibleCategory
import Mathlib.NumberTheory.Padics.PadicNumbers

/-! # Tests for the abelian category of weakly admissible filtered `(φ, N)`-modules

Over `K₀ = K = ℚ_[p]`, whose absolute Frobenius is the identity, with the `p`-adic valuation:
the category of weakly admissible filtered `(φ, N)`-modules is abelian and `ℚ_[p]`-linear, and
the forgetful functor to `ℚ_[p]`-vector spaces is faithful, exact and conservative; the objects
`ℚ_[p](n)` (with `φ = p ^ n` and the filtration jumping at `n`) give concrete kernels.
For a general `σ`, the category is linear over the subfield fixed by `σ`, and a multiple
`c • η` of a nonzero morphism by `c ∈ K₀` with `σ c ≠ c` is not a morphism.
-/

open CategoryTheory Limits Module TensorProduct FilteredPhiNModule

namespace MathlibExtTest.RingTheory.PhiNModule.WeaklyAdmissibleCategory

noncomputable section

variable {p : ℕ} [Fact p.Prime]

/-- The `p`-adic valuation is invariant under the absolute Frobenius `RingHom.id ℚ_[p]`. -/
theorem padic_hv (x : ℚ_[p]) : Padic.addValuation (RingHom.id ℚ_[p] x) = Padic.addValuation x :=
  rfl

/-- The prime `p` is nonzero in `ℚ_[p]`. -/
theorem p_ne_zero : (p : ℚ_[p]) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero

/-- The filtered `φ`-module `ℚ_[p](n)` on `ℚ_[p]`: `φ = p ^ n • id`, `N = 0`, and the filtration
of `ℚ_[p] ⊗ ℚ_[p]` with a single jump at `n`. -/
def line (n : ℕ) : FilteredPhiNModule (RingHom.id ℚ_[p]) (p : ℚ_[p]) ℚ_[p] ℚ_[p] where
  toPhiNModule := PhiNModule.ofPhi
    (LinearEquiv.smulOfNeZero ℚ_[p] ℚ_[p] ((p : ℚ_[p]) ^ n) (pow_ne_zero n p_ne_zero))
  fil := DecreasingFiltration.single n

/-- `ℚ_[p](n)` has Hodge number `n` and Newton number `n`, so it is weakly admissible. -/
theorem isWeaklyAdmissible_line (n : ℕ) :
    (line (p := p) n).IsWeaklyAdmissible Padic.addValuation := by
  rw [isWeaklyAdmissible_iff_of_finrank_eq_one _ padic_hv (finrank_self ℚ_[p])]
  have hH : (line (p := p) n).hodgeNumber = n := by
    rw [hodgeNumber, line, DecreasingFiltration.hodgeNumber_single, Module.finrank_baseChange,
      finrank_self, Nat.cast_one, mul_one]
  have h := PhiNModule.coe_newtonNumber _ padic_hv (line (p := p) n).toPhiNModule
    (Basis.singleton (Fin 1) ℚ_[p])
  have hdet : (Basis.singleton (Fin 1) ℚ_[p]).det
      ((line (p := p) n).φ ∘ Basis.singleton (Fin 1) ℚ_[p]) = (p : ℚ_[p]) ^ n := by
    rw [Basis.det_apply, Matrix.det_unique]
    simp [line, Basis.toMatrix_apply]
  rw [hdet, AddValuation.map_pow, Padic.addValuation.apply p_ne_zero, Padic.valuation_p] at h
  have h' : n • ((1 : ℤ) : WithTop ℤ) = ((n : ℤ) : WithTop ℤ) := by
    rw [← WithTop.coe_nsmul, nsmul_one]
  rw [hH]
  exact_mod_cast (h.trans h').symm

/-- The `p`-adic valuation is invariant under the absolute Frobenius `RingHom.id ℚ_[p]`. -/
instance factPadicHv :
    Fact (∀ x : ℚ_[p], Padic.addValuation (RingHom.id ℚ_[p] x) = Padic.addValuation x) :=
  ⟨padic_hv⟩

/-- The absolute Frobenius `RingHom.id ℚ_[p]` fixes `ℚ_[p]`. -/
instance factPadicFixed :
    Fact (∀ r : ℚ_[p], RingHom.id ℚ_[p] (algebraMap ℚ_[p] ℚ_[p] r) = algebraMap ℚ_[p] ℚ_[p] r) :=
  ⟨fun _ => rfl⟩

/-- The category of weakly admissible filtered `φ`-modules over `ℚ_[p]` in `Type`. -/
abbrev C (p : ℕ) [Fact p.Prime] : Type 1 :=
  WeaklyAdmissibleCat.{0} (RingHom.id ℚ_[p]) (p : ℚ_[p]) ℚ_[p] Padic.addValuation

example : Abelian (C p) := inferInstance
example : Linear ℚ_[p] (C p) := inferInstance
example : HasZeroObject (C p) := inferInstance
example : HasFiniteBiproducts (C p) := inferInstance
example : HasKernels (C p) := inferInstance
example : HasCokernels (C p) := inferInstance

/-- The forgetful functor of `C p` to `ℚ_[p]`-vector spaces. -/
abbrev F (p : ℕ) [Fact p.Prime] : C p ⥤ ModuleCat.{0} ℚ_[p] :=
  WeaklyAdmissibleCat.forgetToModuleCat (RingHom.id ℚ_[p]) (p : ℚ_[p]) ℚ_[p] Padic.addValuation

example : (F p).Faithful := inferInstance
example : (F p).Additive := inferInstance
example : PreservesFiniteLimits (F p) := inferInstance
example : PreservesFiniteColimits (F p) := inferInstance
example : (F p).ReflectsIsomorphisms := inferInstance

/-- `ℚ_[p](n)`, with the filtration jumping at `n`, as an object of `C p`. -/
abbrev obj (n : ℕ) : C p :=
  WeaklyAdmissibleCat.of ℚ_[p] (line n) (isWeaklyAdmissible_line n)

/-- `ℚ_[p](n) ⊕ ℚ_[p](m)` as an object of `C p`. -/
abbrev objProd (n m : ℕ) : C p :=
  WeaklyAdmissibleCat.of (ℚ_[p] × ℚ_[p]) ((line n).prod (line m))
    ((isWeaklyAdmissible_line n).prod padic_hv (isWeaklyAdmissible_line m))

/-- The first projection `ℚ_[p](n) ⊕ ℚ_[p](m) ⟶ ℚ_[p](n)` as a morphism of `C p`. -/
abbrev fstHom (p : ℕ) [Fact p.Prime] (n m : ℕ) : objProd (p := p) n m ⟶ obj n :=
  FilteredPhiNModule.fst (line n) (line m)

/-- The underlying space of the kernel of the first projection is its kernel as a linear map,
and its filtration is induced from `ℚ_[p](n) ⊕ ℚ_[p](m)`. -/
example (n m : ℕ) : (WeaklyAdmissibleCat.kernelFork (fstHom p n m)).pt.carrier =
    LinearMap.ker (LinearMap.fst ℚ_[p] ℚ_[p] ℚ_[p]) :=
  rfl

/-- The kernel of the first projection is a limit, so it computes `kernel`. -/
example (n m : ℕ) :
    kernel (fstHom p n m) ≅ (WeaklyAdmissibleCat.kernelFork (fstHom p n m)).pt :=
  (limit.isLimit _).conePointUniqueUpToIso (WeaklyAdmissibleCat.kernelIsLimit _)

/-- The forgetful functor sends a morphism to its underlying linear map. -/
example (n m : ℕ) : ((F p).map (fstHom p n m)).hom = LinearMap.fst ℚ_[p] ℚ_[p] ℚ_[p] :=
  rfl

/-- The identity of an object has the identity as underlying linear map. -/
example (n : ℕ) : (𝟙 (obj (p := p) n) : obj n ⟶ obj n).toLinearMap = LinearMap.id := by
  simp

/-- Scalar multiples by `ℚ_[p]` of morphisms are computed on the underlying linear maps. -/
example (n m : ℕ) (c : ℚ_[p]) : (c • fstHom p n m : objProd n m ⟶ obj n).toLinearMap =
    c • LinearMap.fst ℚ_[p] ℚ_[p] ℚ_[p] := by
  simp

/-- A morphism of `C p` whose underlying linear map is bijective is an isomorphism. -/
example {X Y : C p} (f : X ⟶ Y) (hf : Function.Bijective f.toLinearMap) : IsIso f := by
  have : IsIso ((F p).map f) := (LinearEquiv.ofBijective f.toLinearMap hf).toModuleIso.isIso_hom
  exact isIso_of_reflects_iso f (F p)

section General

variable {K₀ : Type} [Field K₀] (σ : K₀ →+* K₀) {σ' : K₀ →+* K₀} [RingHomInvPair σ σ']
  [RingHomInvPair σ' σ] (p₀ : K₀) (K : Type) [Field K] [Algebra K₀ K]
  (v : AddValuation K₀ (WithTop ℤ))

/-- The subfield of `K₀` fixed by `σ` is fixed by `σ`. -/
instance factEqLocus :
    Fact (∀ r : σ.eqLocusField (RingHom.id K₀),
      σ (algebraMap (σ.eqLocusField (RingHom.id K₀)) K₀ r) =
        algebraMap (σ.eqLocusField (RingHom.id K₀)) K₀ r) :=
  ⟨fun r => r.2⟩

/-- The category is linear over the subfield of `K₀` fixed by `σ`. -/
example : Linear (σ.eqLocusField (RingHom.id K₀)) (WeaklyAdmissibleCat.{0} σ p₀ K v) :=
  inferInstance

/-- For `v ∘ σ = v`, the category is abelian. -/
example [Fact (∀ x, v (σ x) = v x)] : Abelian (WeaklyAdmissibleCat.{0} σ p₀ K v) :=
  inferInstance

/-- The multiple `c • η` of a morphism `η` of `(φ, N)`-modules by `c ∈ K₀` with `σ c ≠ c` is
not a morphism if `φ ∘ η ≠ 0`: morphisms do not form a `K₀`-module. -/
example {D₁ D₂ : Type} [AddCommGroup D₁] [Module K₀ D₁] [AddCommGroup D₂] [Module K₀ D₂]
    {M₁ : _root_.PhiNModule σ p₀ D₁} {M₂ : _root_.PhiNModule σ p₀ D₂} (η : M₁.Hom M₂)
    {x : D₁} (hx : η.toLinearMap x ≠ 0) {c : K₀} (hc : σ c ≠ c) :
    ¬ ∃ η' : M₁.Hom M₂, η'.toLinearMap = c • η.toLinearMap := by
  rintro ⟨η', hη'⟩
  obtain ⟨y, rfl⟩ := M₁.φ.surjective x
  have h := η'.map_φ y
  rw [hη', LinearMap.smul_apply, LinearMap.smul_apply, η.map_φ, LinearEquiv.map_smulₛₗ] at h
  have h0 : (σ c - c) • M₂.φ (η.toLinearMap y) = 0 := by
    rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp h0 with h1 | h1
  · exact hc (sub_eq_zero.mp h1)
  · rw [map_eq_zero_iff _ M₂.φ.injective] at h1
    rw [η.map_φ, h1, map_zero] at hx
    exact hx rfl

end General

end

end MathlibExtTest.RingTheory.PhiNModule.WeaklyAdmissibleCategory
