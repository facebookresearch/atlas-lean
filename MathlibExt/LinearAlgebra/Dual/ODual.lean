/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.LinearAlgebra.BilinearMap

/-!
# The `O`-linear dual of a module over an `O`-algebra

Let `O` be a commutative ring and `A` a commutative `O`-algebra. For an `A`-module `N` (with
compatible `O`-module structure), `Module.ODual O A N` is the `O`-linear dual
`N^* = Hom_O(N, O)`, an `A`-module by `(a • φ) n = φ (a • n)`; for `N = A` it is
`ω_A = Hom_O(A, O)`, an `A`-module by `(a • λ) x = λ (a x)`. Then:

* `Module.ODual.homEquiv M : Hom_A(M, ω_A) ≃ₗ[A] M^*`, `Φ_M ψ m = ψ m 1`, is an isomorphism of
  `A`-modules, with inverse `φ ↦ (m ↦ (a ↦ φ (a • m)))` (`Module.ODual.homEquiv_apply`,
  `Module.ODual.homEquiv_symm_apply_apply`);
* for an `A`-linear `f : M → M'`, the `O`-dual `f^* : φ ↦ φ ∘ f` is `A`-linear
  (`Module.ODual.dualMap`), and `Φ` is natural: `Φ_M (ψ ∘ f) = f^* (Φ_{M'} ψ)`
  (`Module.ODual.homEquiv_comp`); in particular `Φ_M` carries `ψ ↦ ψ ∘ f` on `Hom_A(M, ω_A)` to
  `f^*` on `M^*`;
* for an isomorphism of `A`-modules `h : A ≃ ω_A`, `ψ ↦ Φ_M (h ∘ ψ) = h(1) ∘ ψ` is an isomorphism
  of `A`-modules `Hom_A(M, A) ≃ M^*` (`Module.ODual.homEquivOfLinearEquiv`,
  `Module.ODual.homEquivOfLinearEquiv_apply`).

Each assertion is a direct check from the formulas.

## References

* B. Conrad, *The Shimura construction in weight 2*, appendix to K. A. Ribet and W. A. Stein,
  *Lectures on Serre's conjectures*, IAS/Park City Math. Ser.: §5.3, proof of Lemma 5.17, p. 71
  ("Choose an isomorphism h : A ≅ Hom_O(A, O) as A-modules, so the projections
  π_i : M → A e_i ≅ A satisfy e_i^* = h(i) ∘ π_i in M^*"), where the printed `h(i)` is `h(1)`.
-/

@[expose] public section

set_option autoImplicit false

set_option linter.unusedVariables false in
/-- The `O`-linear dual `Hom_O(N, O)` of an `A`-module `N`, with the `A`-module structure
`(a • φ) n = φ (a • n)`. As a type it is `N →ₗ[O] O`. -/
def Module.ODual (O A N : Type*) [CommRing O] [AddCommGroup N] [Module O N] : Type _ :=
  N →ₗ[O] O

namespace Module.ODual

section Basic

variable (O A N : Type*) [CommRing O] [AddCommGroup N] [Module O N]

instance : AddCommGroup (ODual O A N) := inferInstanceAs (AddCommGroup (N →ₗ[O] O))

instance : FunLike (ODual O A N) N O := inferInstanceAs (FunLike (N →ₗ[O] O) N O)

instance : LinearMapClass (ODual O A N) O N O := inferInstanceAs (LinearMapClass (N →ₗ[O] O) O N O)

variable {O A N} in
/-- An `O`-linear map `N → O`, as an element of `ODual O A N`. -/
def ofLinearMap : (N →ₗ[O] O) ≃+ ODual O A N := AddEquiv.refl _

variable {O A N} in
/-- An element of `ODual O A N`, as an `O`-linear map `N → O`. -/
def toLinearMap : ODual O A N ≃+ (N →ₗ[O] O) := AddEquiv.refl _

variable {O A N} in
@[ext] theorem ext {φ ψ : ODual O A N} (h : ∀ n, φ n = ψ n) : φ = ψ := LinearMap.ext h

variable {O A N} in
@[simp] theorem ofLinearMap_apply (φ : N →ₗ[O] O) (n : N) : (ofLinearMap φ : ODual O A N) n = φ n :=
  rfl

variable {O A N} in
@[simp] theorem toLinearMap_apply (φ : ODual O A N) (n : N) : toLinearMap φ n = φ n := rfl

variable {O A N} in
@[simp] theorem add_apply (φ ψ : ODual O A N) (n : N) : (φ + ψ) n = φ n + ψ n := rfl

end Basic

variable (O A : Type*) [CommRing O] [CommRing A] [Algebra O A]
variable (N : Type*) [AddCommGroup N] [Module A N] [Module O N] [IsScalarTower O A N]

instance : Module A (ODual O A N) where
  smul a φ := ofLinearMap (toLinearMap φ ∘ₗ (LinearMap.lsmul A N a).restrictScalars O)
  one_smul φ := by ext n; change φ ((1 : A) • n) = φ n; rw [one_smul]
  mul_smul a b φ := by ext n; change φ ((a * b) • n) = φ (b • a • n); rw [smul_smul, mul_comm]
  smul_zero a := by ext; rfl
  smul_add a φ ψ := by ext; rfl
  add_smul a b φ := by ext n; change φ ((a + b) • n) = φ (a • n) + φ (b • n); rw [add_smul, map_add]
  zero_smul φ := by ext n; change φ ((0 : A) • n) = 0; rw [zero_smul, map_zero]

variable {O A N} in
@[simp] theorem smul_apply (a : A) (φ : ODual O A N) (n : N) : (a • φ) n = φ (a • n) := rfl

instance : SMulCommClass A A (ODual O A A) where
  smul_comm a b φ := by
    ext x
    simp only [smul_apply, smul_smul, mul_comm]

variable {O A}
variable (M : Type*) [AddCommGroup M] [Module A M] [Module O M] [IsScalarTower O A M]

/-- **The `O`-linear dual of a module over an `O`-algebra.** Let $\mathcal{O}$ be a commutative
ring, $A$ a commutative $\mathcal{O}$-algebra,
$\omega_A = \operatorname{Hom}_{\mathcal{O}}(A, \mathcal{O})$, an $A$-module by
$(a\lambda)(x) = \lambda(ax)$, and for an $A$-module $M$ let
$M^* = \operatorname{Hom}_{\mathcal{O}}(M, \mathcal{O})$, an $A$-module by
$(a\varphi)(m) = \varphi(am)$. Then
$$\Phi_M \colon \operatorname{Hom}_A(M, \omega_A) \to M^*, \qquad \Phi_M(\psi)(m) = \psi(m)(1),$$
is an isomorphism of $A$-modules, with inverse sending $\varphi$ to
$m \mapsto (a \mapsto \varphi(am))$. Here $\omega_A$ is `Module.ODual O A A` and $M^*$ is
`Module.ODual O A M`.

Source: B. Conrad, *The Shimura construction in weight 2*, appendix to K. A. Ribet and
W. A. Stein, *Lectures on Serre's conjectures*, §5.3, proof of Lemma 5.17, p. 71. -/
noncomputable def homEquiv : (M →ₗ[A] ODual O A A) ≃ₗ[A] ODual O A M where
  toFun ψ := ofLinearMap
    { toFun := fun m => ψ m 1
      map_add' := fun m m' => by rw [map_add]; rfl
      map_smul' := fun c m => by
        rw [← algebraMap_smul A c m, map_smul, smul_apply, RingHom.id_apply,
          algebraMap_smul, map_smul, smul_eq_mul] }
  map_add' ψ ψ' := by ext; rfl
  map_smul' a ψ := by
    ext m
    change (a • ψ m) 1 = ψ (a • m) 1
    rw [map_smul]
  invFun φ :=
    { toFun := fun m => ofLinearMap
        { toFun := fun x => φ (x • m)
          map_add' := fun x y => by rw [add_smul, map_add]
          map_smul' := fun c x => by rw [smul_assoc, map_smul, RingHom.id_apply] }
      map_add' := fun m m' => by ext x; simp [smul_add]
      map_smul' := fun a m => by
        ext x
        change φ (x • a • m) = φ ((a • x) • m)
        rw [smul_smul, smul_eq_mul, mul_comm] }
  left_inv ψ := by
    ext m x
    change ψ (x • m) 1 = ψ m x
    rw [map_smul, smul_apply, smul_eq_mul, mul_one]
  right_inv φ := by
    ext m
    change φ ((1 : A) • m) = φ m
    rw [one_smul]

variable {M}

@[simp] theorem homEquiv_apply (ψ : M →ₗ[A] ODual O A A) (m : M) : homEquiv M ψ m = ψ m 1 := rfl

@[simp] theorem homEquiv_symm_apply_apply (φ : ODual O A M) (m : M) (x : A) :
    (homEquiv M).symm φ m x = φ (x • m) := rfl

variable {M' : Type*} [AddCommGroup M'] [Module A M'] [Module O M'] [IsScalarTower O A M']

/-- The `O`-dual `f^* : φ ↦ φ ∘ f` of an `A`-linear map `f : M → M'`; it is `A`-linear. -/
def dualMap (f : M →ₗ[A] M') : ODual O A M' →ₗ[A] ODual O A M where
  toFun φ := ofLinearMap (toLinearMap φ ∘ₗ f.restrictScalars O)
  map_add' φ φ' := by ext; rfl
  map_smul' a φ := by
    ext m
    change φ (a • f m) = φ (f (a • m))
    rw [LinearMap.map_smul f a m]

@[simp] theorem dualMap_apply (f : M →ₗ[A] M') (φ : ODual O A M') (m : M) :
    dualMap f φ m = φ (f m) := rfl

/-- **Naturality of `Φ`.** For every $A$-linear $f \colon M \to M'$ and
$\psi \in \operatorname{Hom}_A(M', \omega_A)$, $\Phi_M(\psi \circ f) = \Phi_{M'}(\psi) \circ f$.
In particular, for an $A$-linear $f \colon M \to M$, $\Phi_M$ carries $\psi \mapsto \psi \circ f$
on $\operatorname{Hom}_A(M, \omega_A)$ to the $\mathcal{O}$-dual
$f^* \colon \varphi \mapsto \varphi \circ f$ on $M^*$ (`Module.ODual.dualMap f`), which is
$A$-linear.

Source: B. Conrad, *The Shimura construction in weight 2*, appendix to K. A. Ribet and
W. A. Stein, *Lectures on Serre's conjectures*, §5.3, proof of Lemma 5.17, p. 71. -/
theorem homEquiv_comp (f : M →ₗ[A] M') (ψ : M' →ₗ[A] ODual O A A) :
    homEquiv M (ψ ∘ₗ f) = dualMap f (homEquiv M' ψ) := rfl

/-- For an isomorphism of `A`-modules `h : A ≃ ω_A`, the isomorphism of `A`-modules
`Hom_A(M, A) ≃ M^*`, `ψ ↦ Φ_M (h ∘ ψ)`. -/
noncomputable def homEquivOfLinearEquiv (h : A ≃ₗ[A] ODual O A A) :
    (M →ₗ[A] A) ≃ₗ[A] ODual O A M :=
  (LinearEquiv.congrRight h).trans (homEquiv M)

/-- If $h \colon A \to \omega_A$ is an isomorphism of $A$-modules, then the isomorphism of
$A$-modules $\operatorname{Hom}_A(M, A) \cong M^*$, $\psi \mapsto \Phi_M(h \circ \psi)$, is
$\psi \mapsto h(1) \circ \psi$.

Source: B. Conrad, *The Shimura construction in weight 2*, appendix to K. A. Ribet and
W. A. Stein, *Lectures on Serre's conjectures*, §5.3, proof of Lemma 5.17, p. 71. -/
theorem homEquivOfLinearEquiv_apply (h : A ≃ₗ[A] ODual O A A) (ψ : M →ₗ[A] A) (m : M) :
    homEquivOfLinearEquiv h ψ m = h 1 (ψ m) := by
  change h (ψ m) 1 = h 1 (ψ m)
  rw [← mul_one (ψ m), ← smul_eq_mul, map_smul, smul_apply, smul_eq_mul, mul_one]

end Module.ODual

end
