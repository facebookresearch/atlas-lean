/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Fold
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Tactic.NoncommRing

/-!
# Exterior derivations induced by linear endomorphisms

Let R be a commutative ring and M an R-module. Every R-linear endomorphism g of M extends to a
unique ordinary R-linear derivation D_g of E=ExteriorAlgebra(R,M), with D_g(r)=0 and
D_g(ι(x))=ι(gx). Its Leibniz law is D_g(ab)=D_g(a)b+aD_g(b), with the product order unchanged.
Since D_g preserves exterior degree, it has degree zero and no Koszul sign occurs in this law.

The assignment g ↦ D_g is R-linear, preserves commutators and is natural for module maps
intertwining the endomorphisms. It therefore gives a homomorphism between the commutator Lie
algebras of End_R(M) and End_R(E). No basis or characteristic assumption is required, and
source, target-module and ring universes are arbitrary.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w

namespace ExteriorAlgebra

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

private def derivationStep (g : Module.End R M) :
    M →ₗ[R] (ExteriorAlgebra R M × ExteriorAlgebra R M) →ₗ[R]
      ExteriorAlgebra R M :=
  (((Algebra.lmul R (ExteriorAlgebra R M)).toLinearMap.comp
      ((ι R).comp g)).compl₂
    (LinearMap.fst R (ExteriorAlgebra R M) (ExteriorAlgebra R M))) +
  (((Algebra.lmul R (ExteriorAlgebra R M)).toLinearMap.comp
      (ι R)).compl₂
    (LinearMap.snd R (ExteriorAlgebra R M) (ExteriorAlgebra R M)))

private lemma derivationStep_apply (g : Module.End R M) (x : M)
    (a : ExteriorAlgebra R M × ExteriorAlgebra R M) :
    derivationStep R M g x a = ι R (g x) * a.1 + ι R x * a.2 :=
  rfl

private theorem derivationStep_relation (g : Module.End R M)
    (x : M) (a b : ExteriorAlgebra R M) :
    derivationStep R M g x
        (ι R x * a, derivationStep R M g x (a, b)) =
      (0 : QuadraticForm R M) x • b := by
  have hanti : ι R (g x) * ι R x + ι R x * ι R (g x) = 0 :=
    ι_add_mul_swap (g x) x
  have hz : (0 : QuadraticForm R M) x • b = (0 : ExteriorAlgebra R M) := by
    simp
  rw [hz]
  change ι R (g x) * (ι R x * a) +
    ι R x * (ι R (g x) * a + ι R x * b) = 0
  calc
    _ = (ι R (g x) * ι R x + ι R x * ι R (g x)) * a +
        (ι R x * ι R x) * b := by noncomm_ring
    _ = 0 := by rw [hanti, ι_sq_zero, zero_mul, zero_mul, add_zero]

private def derivationAux (g : Module.End R M) :
    Module.End R (ExteriorAlgebra R M) :=
  CliffordAlgebra.foldr' (0 : QuadraticForm R M)
    (derivationStep R M g) (derivationStep_relation R M g) 0

private theorem derivationAux_algebraMap (g : Module.End R M) (r : R) :
    derivationAux R M g (algebraMap R (ExteriorAlgebra R M) r) = 0 := by
  simp [derivationAux, CliffordAlgebra.foldr'_algebraMap]

private theorem derivationAux_ι_mul (g : Module.End R M) (x : M)
    (a : ExteriorAlgebra R M) :
    derivationAux R M g (ι R x * a) =
      ι R (g x) * a + ι R x * derivationAux R M g a := by
  simpa only [derivationAux, derivationStep_apply] using
    (CliffordAlgebra.foldr'_ι_mul (0 : QuadraticForm R M)
      (derivationStep R M g) (derivationStep_relation R M g)
      (0 : ExteriorAlgebra R M) x a)

private theorem derivationAux_add (g h : Module.End R M) :
    derivationAux R M (g + h) = derivationAux R M g + derivationAux R M h := by
  apply LinearMap.ext
  intro a
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r =>
      simp only [LinearMap.add_apply, derivationAux_algebraMap, add_zero]
  | add a b ha hb =>
      simp only [LinearMap.add_apply, map_add, ha, hb]
  | ι_mul a x ha =>
      simp only [LinearMap.add_apply, derivationAux_ι_mul, map_add,
        ha, add_mul, mul_add]; abel

private theorem derivationAux_smul (r : R) (g : Module.End R M) :
    derivationAux R M (r • g) = r • derivationAux R M g := by
  apply LinearMap.ext
  intro a
  induction a using CliffordAlgebra.left_induction with
  | algebraMap t =>
      simp only [LinearMap.smul_apply, derivationAux_algebraMap, smul_zero]
  | add a b ha hb =>
      simp only [LinearMap.smul_apply, map_add, ha, hb]
  | ι_mul a x ha =>
      simp only [LinearMap.smul_apply, derivationAux_ι_mul, map_smul,
        ha, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_add]

/-- Let R be a commutative ring, M an R-module with additive inverses and E=ExteriorAlgebra(R,M).
For g ∈ End_R(M), write D_g for its induced exterior derivation. The assignment g ↦ D_g is
R-linear from End_R(M) to End_R(E). It is characterized by D_g(r)=0 on scalars, D_g(ι(x))=ι(gx)
on generators and the ordinary Leibniz law D_g(ab)=D_g(a)b+aD_g(b). -/
def derivation : Module.End R M →ₗ[R] Module.End R (ExteriorAlgebra R M) where
  toFun := private derivationAux R M
  map_add' := by exact derivationAux_add R M
  map_smul' := by exact derivationAux_smul R M

/-- Let R be a commutative ring, M an R-module with additive inverses and E=ExteriorAlgebra(R,M).
For g ∈ End_R(M), write D_g for its induced exterior derivation. For r ∈ R,
D_g(algebraMap(r))=0. -/
@[simp]
theorem derivation_algebraMap (g : Module.End R M) (r : R) :
    derivation R M g (algebraMap R (ExteriorAlgebra R M) r) = 0 :=
  derivationAux_algebraMap R M g r

/-- Let R be a commutative ring, M an R-module with additive inverses and E=ExteriorAlgebra(R,M).
For g ∈ End_R(M), write D_g for its induced exterior derivation. For every g ∈ End_R(M),
D_g(1_E)=0. -/
@[simp]
theorem derivation_one (g : Module.End R M) :
    derivation R M g 1 = 0 := by
  simpa only [map_one] using derivation_algebraMap R M g 1

/-- Let R be a commutative ring, M an R-module with additive inverses and E=ExteriorAlgebra(R,M).
For g ∈ End_R(M), write D_g for its induced exterior derivation. For x ∈ M and a ∈ E,
D_g(ι(x)·a)=ι(gx)·a+ι(x)·D_g(a). The product order is retained and there is no graded sign
because D_g has degree zero. -/
@[simp]
theorem derivation_ι_mul (g : Module.End R M) (x : M)
    (a : ExteriorAlgebra R M) :
    derivation R M g (ι R x * a) =
      ι R (g x) * a + ι R x * derivation R M g a :=
  derivationAux_ι_mul R M g x a

/-- Let R be a commutative ring, M an R-module with additive inverses and E=ExteriorAlgebra(R,M).
For g ∈ End_R(M), write D_g for its induced exterior derivation. For x ∈ M, D_g(ι(x))=ι(gx). -/
@[simp]
theorem derivation_ι (g : Module.End R M) (x : M) :
    derivation R M g (ι R x) = ι R (g x) := by
  simpa only [mul_one, derivation_one, mul_zero, add_zero] using
    derivation_ι_mul R M g x 1

/-- Let R be a commutative ring, M an R-module with additive inverses and E=ExteriorAlgebra(R,M).
For g ∈ End_R(M), write D_g for its induced exterior derivation. For all a,b ∈ E,
D_g(ab)=D_g(a)b+aD_g(b). The exterior algebra may be noncommutative; this degree-zero derivation
uses the indicated order of products. -/
theorem derivation_mul (g : Module.End R M) (a b : ExteriorAlgebra R M) :
    derivation R M g (a * b) =
      derivation R M g a * b + a * derivation R M g b := by
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r =>
      simp only [← Algebra.smul_def, map_smul, derivation_algebraMap,
        zero_mul, zero_add]
  | add a a' ha ha' =>
      simp only [add_mul, map_add, ha, ha']; abel
  | ι_mul a x ha =>
      rw [mul_assoc, derivation_ι_mul, ha, derivation_ι_mul]
      noncomm_ring

/-- Let R be a commutative ring, M an R-module with additive inverses and E=ExteriorAlgebra(R,M).
For g ∈ End_R(M), write D_g for its induced exterior derivation. If an R-linear endomorphism D:E
→ E vanishes on every scalar and satisfies D(ι(x)a)=ι(gx)a+ι(x)D(a) for all x,a, then D=D_g. -/
theorem derivation_unique (g : Module.End R M)
    (D : Module.End R (ExteriorAlgebra R M))
    (hR : ∀ r : R, D (algebraMap R (ExteriorAlgebra R M) r) = 0)
    (hι : ∀ (x : M) (a : ExteriorAlgebra R M),
      D (ι R x * a) = ι R (g x) * a + ι R x * D a) :
    D = derivation R M g := by
  apply LinearMap.ext
  intro a
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r => rw [hR, derivation_algebraMap]
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | ι_mul a x ha => rw [hι, derivation_ι_mul, ha]

/-- Let R be a commutative ring, M an R-module with additive inverses and E=ExteriorAlgebra(R,M).
For g ∈ End_R(M), write D_g for its induced exterior derivation. For n : ℕ and a ∈ E with a ∈
∧ⁿ_RM, one has D_g(a) ∈ ∧ⁿ_RM. Thus the induced derivation has exterior degree zero. -/
theorem derivation_mem_exteriorPower (g : Module.End R M) (n : ℕ)
    (a : ExteriorAlgebra R M) (ha : a ∈ ⋀[R]^n M) :
    derivation R M g a ∈ ⋀[R]^n M := by
  dsimp only [ExteriorAlgebra.exteriorPower] at ha ⊢
  induction ha using Submodule.pow_induction_on_left' with
  | algebraMap r =>
      rw [derivation_algebraMap]
      exact Submodule.zero_mem _
  | add a b n ha hb iha ihb =>
      rw [map_add]
      exact Submodule.add_mem _ iha ihb
  | mem_mul m hm n a ha ih =>
      obtain ⟨x, rfl⟩ := hm
      rw [derivation_ι_mul, pow_succ']
      exact Submodule.add_mem _
        (Submodule.mul_mem_mul (LinearMap.mem_range_self _ (g x)) ha)
        (Submodule.mul_mem_mul (LinearMap.mem_range_self _ x) ih)

/-- Let R be a commutative ring, M an R-module with additive inverses and E=ExteriorAlgebra(R,M).
For g ∈ End_R(M), write D_g for its induced exterior derivation. For g,h ∈ End_R(M),
D_{g∘h-h∘g}=D_g∘D_h-D_h∘D_g as R-linear endomorphisms of E. -/
theorem derivation_commutator (g h : Module.End R M) :
    derivation R M (g.comp h - h.comp g) =
      (derivation R M g).comp (derivation R M h) -
        (derivation R M h).comp (derivation R M g) := by
  apply LinearMap.ext
  intro a
  change derivation R M (g.comp h - h.comp g) a =
    derivation R M g (derivation R M h a) -
      derivation R M h (derivation R M g a)
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r => simp only [derivation_algebraMap, map_zero, sub_self]
  | add a b ha hb => simp only [map_add, ha, hb]; noncomm_ring
  | ι_mul a x ha =>
      rw [derivation_ι_mul, ha]
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, map_sub,
        derivation_ι_mul, map_add]; noncomm_ring

/-- Let R be a commutative ring and M,N be R-modules in arbitrary universes. If f:M →ₗ[R] N,
g∈End_R(M), h∈End_R(N) satisfy f∘g=h∘f, then ExteriorAlgebra.map(f)∘D_g =
D_h∘ExteriorAlgebra.map(f). -/
theorem derivation_naturality
    {N : Type w} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (g : Module.End R M) (h : Module.End R N)
    (hfg : f.comp g = h.comp f) :
    (ExteriorAlgebra.map f).toLinearMap.comp (derivation R M g) =
      (derivation R N h).comp (ExteriorAlgebra.map f).toLinearMap := by
  have hinter (x : M) : f (g x) = h (f x) := LinearMap.congr_fun hfg x
  apply LinearMap.ext
  intro a
  change ExteriorAlgebra.map f (derivation R M g a) =
    derivation R N h (ExteriorAlgebra.map f a)
  induction a using CliffordAlgebra.left_induction with
  | algebraMap r =>
      rw [derivation_algebraMap, map_zero, AlgHom.commutes, derivation_algebraMap]
  | add a b ha hb => simp only [map_add, ha, hb]
  | ι_mul a x ha =>
      simp only [derivation_ι_mul, map_mul, map_add,
        ExteriorAlgebra.map_apply_ι, hinter, ha]

section Lie

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Let R be a commutative ring, M an R-module with additive inverses and E=ExteriorAlgebra(R,M).
For g ∈ End_R(M), write D_g for its induced exterior derivation. The R-linear extension End_R(M)
→ End_R(E), g ↦ D_g, is a homomorphism of the commutator Lie algebras with bracket
[g,h]=g∘h-h∘g. -/
def derivationLieHom :
    Module.End R M →ₗ⁅R⁆ Module.End R (ExteriorAlgebra R M) where
  __ := derivation R M
  map_lie' {g h} := by
    change derivation R M (g * h - h * g) =
      derivation R M g * derivation R M h -
        derivation R M h * derivation R M g
    simpa only [Module.End.mul_eq_comp] using derivation_commutator R M g h

/-- Let R be a commutative ring, M an R-module with additive inverses and E=ExteriorAlgebra(R,M).
For g ∈ End_R(M), write D_g for its induced exterior derivation. The underlying R-linear map of
derivationLieHom R M equals derivation R M, sending g to D_g. -/
@[simp]
theorem derivationLieHom_toLinearMap :
    (derivationLieHom R M).toLinearMap = derivation R M :=
  rfl

end Lie

end ExteriorAlgebra
