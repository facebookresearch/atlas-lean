/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Lift

/-!
# Kähler differentials with augmentation coefficients

Let k→P→A be a compatible tower of commutative rings. The A-module C=A⊗_PΩ¹_{P/k} has the
k-derivation p ↦ 1⊗dp. For an A-module M with compatible restricted P- and k-actions, the
correspondence Hom_A(C,M) ≃ Der_k(P,M) sends f to p ↦ f(1⊗dp), and its inverse sends a
derivation D to a⊗dp ↦ a·D(p). It is A-linear and natural in coefficient module maps; maps from
C are determined by the generators 1⊗dp.

A k-algebra map f:P→Q compatible with the two structural maps to A induces a coefficient
differential map a⊗dp ↦ a⊗d(f(p)). These maps preserve identity and composition. The base ring,
source algebra, coefficient algebra and module targets retain their separate universes.

References: Stacks Project, Section 92.3, Definitions 92.3.1–92.3.2 and Remark 92.3.3; Loday,
Cyclic Homology, second edition, Definition 3.5.3.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v w t

namespace KaehlerDifferential

variable (k : Type u) (P : Type v) (A : Type w)
  [CommRing k] [CommRing P] [CommRing A]
  [Algebra k P] [Algebra P A] [Algebra k A] [IsScalarTower k P A]

/-- Let k,P,A be commutative rings with a compatible algebra tower k→P→A. Put Ω=Ω¹_{P/k} and
C=A⊗_PΩ. Coefficient k P A is the A-module C=A⊗_PΩ¹_{P/k}. It represents k-derivations from P to
A-modules, with P acting through P→A. -/
abbrev Coefficient := A ⊗[P] KaehlerDifferential k P

/-- Let k,P,A be commutative rings with a compatible algebra tower k→P→A. Put Ω=Ω¹_{P/k} and
C=A⊗_PΩ. The map D_C:P → C given by p ↦ 1_A⊗_Pdp is a k-derivation, using the P-action on C
induced through P→A. -/
def coefficientD : Derivation k P (Coefficient k P A) :=
  (TensorProduct.mk P A (KaehlerDifferential k P) (1 : A)).compDer
    (KaehlerDifferential.D k P)

@[simp]
theorem coefficientD_apply (p : P) :
    coefficientD k P A p = (1 : A) ⊗ₜ[P] KaehlerDifferential.D k P p := rfl

section Ext

variable {M : Type t} [AddCommGroup M] [Module A M]

omit [Algebra k A] [IsScalarTower k P A] in
/-- For a k-algebra P and a P-algebra A, put C=A⊗_PΩ¹_{P/k}. A-linear maps f,g:C → M
are equal if f(1⊗dp)=g(1⊗dp) for every p∈P. The A-module M needs no separately supplied
P- or k-action, and no chosen k-algebra structure on A is needed. -/
@[ext]
theorem coefficient_hom_ext {f g : Coefficient k P A →ₗ[A] M}
    (h : ∀ p : P,
      f ((1 : A) ⊗ₜ[P] KaehlerDifferential.D k P p) =
      g ((1 : A) ⊗ₜ[P] KaehlerDifferential.D k P p)) : f = g := by
  let : Module P M := Module.compHom M (algebraMap P A)
  let : IsScalarTower P A M := IsScalarTower.of_compHom P A M
  apply TensorProduct.AlgebraTensorModule.ext
  intro a ω
  have hω : ω ∈ Submodule.span P (Set.range (KaehlerDifferential.D k P)) := by
    rw [KaehlerDifferential.span_range_derivation]
    exact Submodule.mem_top
  have hall : ∀ a : A, f (a ⊗ₜ[P] ω) = g (a ⊗ₜ[P] ω) := by
    induction hω using Submodule.span_induction with
    | mem ω hω =>
      obtain ⟨p, rfl⟩ := hω
      intro a
      have ht : (a ⊗ₜ[P] KaehlerDifferential.D k P p : Coefficient k P A) =
          a • ((1 : A) ⊗ₜ[P] KaehlerDifferential.D k P p) :=
        TensorProduct.tmul_eq_smul_one_tmul a (KaehlerDifferential.D k P p)
      exact (congrArg f ht).trans ((f.map_smul' a _).trans
        ((congrArg (fun x => a • x) (h p)).trans
          ((g.map_smul' a _).symm.trans (congrArg g ht).symm)))
    | zero =>
      intro a
      simp only [TensorProduct.tmul_zero, map_zero]
    | add ω η _ _ hω hη =>
      intro a
      simp only [TensorProduct.tmul_add, map_add, hω a, hη a]
    | smul p ω _ hω =>
      intro a
      simp only [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      exact hω (p • a)
  exact hall a

end Ext

section Universal

variable {M : Type t} [AddCommGroup M]
  [Module A M] [Module P M] [Module k M]
  [IsScalarTower P A M] [IsScalarTower k P M] [IsScalarTower k A M]

/-- For a k-algebra P and a P-algebra A, let M carry compatible module actions with
towers P→A→M and k→P→M. Then Hom_A(A⊗_PΩ¹_{P/k},M) ≃ Der_k(P,M), sending f to
p ↦ f(1⊗dp). The inverse sends D to the A-linear map a⊗dp ↦ a·D(p). No chosen
k-algebra structure on A is needed. -/
def coefficientHomEquivDerivation :
    (Coefficient k P A →ₗ[A] M) ≃ Derivation k P M :=
  (LinearMap.liftBaseChangeEquiv A).symm.toEquiv.trans
    (KaehlerDifferential.linearMapEquivDerivation k P).toEquiv

omit [Algebra k A] [IsScalarTower k P A] [IsScalarTower k A M] in
@[simp]
theorem coefficientHomEquivDerivation_apply
    (f : Coefficient k P A →ₗ[A] M) (p : P) :
    coefficientHomEquivDerivation k P A f p =
      f ((1 : A) ⊗ₜ[P] KaehlerDifferential.D k P p) := rfl

/-- Let k,P,A be commutative rings with a compatible algebra tower k→P→A. Put Ω=Ω¹_{P/k} and
C=A⊗_PΩ. Let M carry compatible A-, P- and k-module structures respecting the three scalar
towers. The universal correspondence Hom_A(C,M) ≃ Der_k(P,M) is an A-linear equivalence, with A
acting on derivations through their values in M. -/
def coefficientLinearMapEquivDerivation :
    (Coefficient k P A →ₗ[A] M) ≃ₗ[A] Derivation k P M where
  __ := coefficientHomEquivDerivation k P A
  map_add' f g := by
    ext p
    rfl
  map_smul' a f := by
    ext p
    rfl

/-- For a k-algebra P and a P-algebra A, let M carry compatible module actions with
towers P→A→M and k→P→M. For D∈Der_k(P,M), coefficientLift k P A D is the A-linear
map A⊗_PΩ¹_{P/k} → M determined by a⊗dp ↦ a·D(p). -/
def coefficientLift (D : Derivation k P M) : Coefficient k P A →ₗ[A] M :=
  D.liftKaehlerDifferential.liftBaseChange A

omit [Algebra k A] [IsScalarTower k P A] [IsScalarTower k A M] in
@[simp]
theorem coefficientLift_tmul_D (D : Derivation k P M) (a : A) (p : P) :
    coefficientLift k P A D (a ⊗ₜ[P] KaehlerDifferential.D k P p) = a • D p := by
  rw [coefficientLift, LinearMap.liftBaseChange_tmul,
    Derivation.liftKaehlerDifferential_comp_D]

omit [Algebra k A] [IsScalarTower k P A] [IsScalarTower k A M] in
@[simp]
theorem coefficientHomEquivDerivation_symm_apply (D : Derivation k P M) :
    (coefficientHomEquivDerivation k P A).symm D = coefficientLift k P A D := rfl

@[simp]
theorem coefficientLift_coefficientD :
    coefficientLift k P A (coefficientD k P A) =
      (LinearMap.id : Coefficient k P A →ₗ[A] Coefficient k P A) := by
  apply (coefficientHomEquivDerivation k P A).injective
  rw [← coefficientHomEquivDerivation_symm_apply,
    Equiv.apply_symm_apply]
  ext p
  rfl

/-- Let k,P,A be commutative rings with a compatible algebra tower k→P→A. Put Ω=Ω¹_{P/k} and
C=A⊗_PΩ. Let M carry compatible A-, P- and k-module structures respecting the three scalar
towers. If D∈Der_k(P,M) and f:C →ₗ[A] M satisfies f(1⊗dp)=D(p) for every p∈P, then
f=coefficientLift k P A D. -/
theorem coefficientLift_unique (D : Derivation k P M)
    (f : Coefficient k P A →ₗ[A] M)
    (h : ∀ p : P, f ((1 : A) ⊗ₜ[P] KaehlerDifferential.D k P p) = D p) :
    f = coefficientLift k P A D := by
  apply coefficient_hom_ext k P A
  intro p
  rw [coefficientLift_tmul_D, one_smul]
  exact h p

variable {N : Type*} [AddCommGroup N]
  [Module A N] [Module P N] [Module k N]
  [IsScalarTower P A N] [IsScalarTower k P N] [IsScalarTower k A N]

omit [Algebra k A] [IsScalarTower k P A] [IsScalarTower k A M] [IsScalarTower k A N] in
/-- For a k-algebra P and a P-algebra A, let M and N have compatible module towers
P→A→M, k→P→M and P→A→N, k→P→N. For an A-linear g:M→N, the derivation
corresponding to g∘f is the P-linear restriction of g postcomposed with the derivation
corresponding to f. No separate k-algebra action on A or k→A→M,N towers are needed. -/
theorem coefficientHomEquivDerivation_naturality
    (g : M →ₗ[A] N) (f : Coefficient k P A →ₗ[A] M) :
    coefficientHomEquivDerivation k P A (g.comp f) =
      (g.restrictScalars P).compDer (coefficientHomEquivDerivation k P A f) := by
  ext p
  rfl

/-- Let k,P,A be commutative rings with a compatible algebra tower k→P→A. Put Ω=Ω¹_{P/k} and
C=A⊗_PΩ. Let M carry compatible A-, P- and k-module structures respecting the three scalar
towers. For a compatible coefficient module N, an A-linear g:M→N and D∈Der_k(P,M), one has
g∘coefficientLift(D)=coefficientLift(g|_P∘D). -/
theorem coefficientLift_naturality (g : M →ₗ[A] N) (D : Derivation k P M) :
    g.comp (coefficientLift k P A D) =
      coefficientLift k P A ((g.restrictScalars P).compDer D) := by
  apply coefficient_hom_ext k P A
  intro p
  simp only [LinearMap.comp_apply, coefficientLift_tmul_D, one_smul]
  rfl

end Universal

section Maps

variable {P A}
variable {Q : Type*} [CommRing Q] [Algebra k Q] [Algebra Q A]
  [IsScalarTower k Q A]

/-- Let k→P→A and k→Q→A be compatible towers of commutative rings. Suppose f:P →ₐ[k] Q satisfies
ρ_P(p)=ρ_Q(f(p)) in A for every p. Then p ↦ 1_A⊗_Qd(f(p)) is a k-derivation P → A⊗_QΩ¹_{Q/k},
with P acting through ρ_P. -/
def coefficientPullback (f : P →ₐ[k] Q)
    (h : ∀ p : P, algebraMap P A p = algebraMap Q A (f p)) :
    Derivation k P (Coefficient k Q A) where
  toLinearMap := (coefficientD k Q A).toLinearMap.comp f.toLinearMap
  map_one_eq_zero' := by
    change coefficientD k Q A (f 1) = 0
    rw [map_one, Derivation.map_one_eq_zero]
  leibniz' p q := by
    change coefficientD k Q A (f (p * q)) =
      p • coefficientD k Q A (f q) + q • coefficientD k Q A (f p)
    rw [map_mul, Derivation.leibniz]
    congr 1
    · rw [← IsScalarTower.algebraMap_smul (R := Q) (A := A),
        ← IsScalarTower.algebraMap_smul (R := P) (A := A), h p]
    · rw [← IsScalarTower.algebraMap_smul (R := Q) (A := A),
        ← IsScalarTower.algebraMap_smul (R := P) (A := A), h q]

omit [Algebra k A] [IsScalarTower k P A] in
@[simp]
theorem coefficientPullback_apply (f : P →ₐ[k] Q)
    (h : ∀ p : P, algebraMap P A p = algebraMap Q A (f p)) (p : P) :
    coefficientPullback k f h p =
      (1 : A) ⊗ₜ[Q] KaehlerDifferential.D k Q (f p) := rfl

/-- Let k→P→A and k→Q→A be compatible commutative-ring towers. If f:P →ₐ[k] Q satisfies ρ_P=ρ_Q∘f,
it induces an A-linear map A⊗_PΩ¹_{P/k} → A⊗_QΩ¹_{Q/k} sending a⊗dp to a⊗d(f(p)). -/
def coefficientMap (f : P →ₐ[k] Q)
    (h : ∀ p : P, algebraMap P A p = algebraMap Q A (f p)) :
    Coefficient k P A →ₗ[A] Coefficient k Q A :=
  coefficientLift k P A (coefficientPullback k f h)

@[simp]
theorem coefficientMap_tmul_D (f : P →ₐ[k] Q)
    (h : ∀ p : P, algebraMap P A p = algebraMap Q A (f p))
    (a : A) (p : P) :
    coefficientMap k f h (a ⊗ₜ[P] KaehlerDifferential.D k P p) =
      a ⊗ₜ[Q] KaehlerDifferential.D k Q (f p) := by
  rw [coefficientMap, coefficientLift_tmul_D, coefficientPullback_apply,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one]

@[simp]
theorem coefficientMap_id :
    coefficientMap k (AlgHom.id k P) (fun _ => rfl) =
      (LinearMap.id : Coefficient k P A →ₗ[A] Coefficient k P A) := by
  apply coefficient_hom_ext k P A
  intro p
  have h := coefficientMap_tmul_D k (P := P) (Q := P) (A := A)
    (AlgHom.id k P) (fun _ => rfl) (1 : A) p
  exact h

variable {T : Type*} [CommRing T] [Algebra k T] [Algebra T A]
  [IsScalarTower k T A]

/-- Let P,Q,T be commutative k-algebras with compatible structural maps to A. If f:P→Q and g:Q→T are
k-algebra maps satisfying ρ_P=ρ_Q∘f and ρ_Q=ρ_T∘g, then
coefficientMap(g∘f)=coefficientMap(g)∘coefficientMap(f). -/
theorem coefficientMap_comp (f : P →ₐ[k] Q) (g : Q →ₐ[k] T)
    (hf : ∀ p : P, algebraMap P A p = algebraMap Q A (f p))
    (hg : ∀ q : Q, algebraMap Q A q = algebraMap T A (g q)) :
    coefficientMap k (g.comp f) (fun p => (hf p).trans (hg (f p))) =
      (coefficientMap k g hg).comp (coefficientMap k f hf) := by
  apply coefficient_hom_ext k P A
  intro p
  simp only [coefficientMap_tmul_D, LinearMap.comp_apply, AlgHom.comp_apply]

end Maps

end KaehlerDifferential

end
