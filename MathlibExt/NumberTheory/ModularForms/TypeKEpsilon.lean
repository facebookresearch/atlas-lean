/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.EigenformWith

/-!
# Modular forms of type `(k, ε)` on `Γ₀(N)`

Let `N ≥ 1` and `k` be integers and `ε` a Dirichlet character mod `N`. Following Deligne–Serre
(§1.5), a *modular form of type `(k, ε)` on `Γ₀(N)`* is a modular form `f` of weight `k` on
`Γ₁(N)` with

`f ((a z + b) / (c z + d)) = ε(d) (c z + d) ^ k f(z)` for all `(a, b; c, d) ∈ Γ₀(N)`.

This file defines:

* `ModularForm.HasNebentypus ε f`: the transformation law of type `(k, ε)` for a modular form
  `f : ModularForm (Gamma1 N) k`, the same condition as `CuspForm.HasNebentypus` for cusp forms;
* `ModularForm.typeSubmodule N k ε`: the `ℂ`-subspace of the modular forms of type `(k, ε)`;
* `ModularForm.IsHeckeEigenvector ε f a`: `f ≠ 0` and `f | T_p = a_p f` for every prime `p ∤ N`,
  with `T_p` given on `q`-expansions by Deligne–Serre's formula (1.6.1).

Deligne and Serre assume `ε(-1) = (-1) ^ k`: otherwise the transformation law for `-1 ∈ Γ₀(N)`
forces `f = 0` (`ModularForm.HasNebentypus.eq_zero_of_ne`).

## References

* P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7
  (1974), 507–530: §1.1, p. 508, for `Γ₁(N)` and `Γ₀(N)`; §1.2, p. 508, for modular forms of
  weight `k`; §1.3, p. 508, for `q`-expansions; §1.5, pp. 508–509, for forms of type `(k, ε)`
  ("On appelle forme modulaire de type (k, ε) sur Γ₀(N) une forme modulaire f de poids k sur
  Γ₁(N) telle que") and the remark that a character and a weight of different parities force
  `f = 0`; formula (1.6.1), p. 509, for `T_p`, `p ∤ N`.
-/

@[expose] public section

set_option autoImplicit false

open CongruenceSubgroup ModularFormClass UpperHalfPlane

open scoped MatrixGroups

namespace ModularForm

variable {N : ℕ} {k : ℤ}

/-- **Modular forms of type `(k, ε)` on `Γ₀(N)`.** Let `ε` be a Dirichlet character mod `N`.
A modular form $f$ of weight $k$ on $\Gamma_1(N)$ has *type* $(k, \varepsilon)$ on
$\Gamma_0(N)$ if
$$f\left(\frac{az+b}{cz+d}\right) = \varepsilon(d)\,(cz+d)^k f(z) \qquad
\text{for all } \begin{pmatrix} a & b \\ c & d \end{pmatrix} \in \Gamma_0(N)$$
and all $z$ in the upper half-plane, where $\varepsilon(d)$ is the value of $\varepsilon$ at the
class of $d$ mod $N$. This is the condition of `CuspForm.HasNebentypus`, for modular forms that
need not be cusp forms.

Source: P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4)
7 (1974), 507–530, §1.5, pp. 508–509. -/
def HasNebentypus (ε : DirichletCharacter ℂ N) (f : ModularForm (Gamma1 N) k) : Prop :=
  ∀ γ : SL(2, ℤ), γ ∈ Gamma0 N → ∀ τ : ℍ,
    f (γ • τ) =
      ε ((γ 1 1 : ℤ) : ZMod N) * ((((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ k * f τ)

/-- **The modular forms of type `(k, ε)` on `Γ₀(N)`**, as a `ℂ`-subspace of the modular forms of
weight $k$ on $\Gamma_1(N)$: the $f$ with `ModularForm.HasNebentypus ε f`.

Source: P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4)
7 (1974), 507–530, §1.5, pp. 508–509. -/
def typeSubmodule (N : ℕ) (k : ℤ) (ε : DirichletCharacter ℂ N) :
    Submodule ℂ (ModularForm (Gamma1 N) k) where
  carrier := {f | HasNebentypus ε f}
  add_mem' {f g} hf hg γ hγ τ := by
    change f (γ • τ) + g (γ • τ) = _ * (_ * (f τ + g τ))
    rw [hf γ hγ τ, hg γ hγ τ]
    ring
  zero_mem' γ _ τ := by simp
  smul_mem' c f hf γ hγ τ := by
    change c * f (γ • τ) = _ * (_ * (c * f τ))
    rw [hf γ hγ τ]
    ring

theorem mem_typeSubmodule {ε : DirichletCharacter ℂ N} {f : ModularForm (Gamma1 N) k} :
    f ∈ typeSubmodule N k ε ↔ HasNebentypus ε f :=
  Iff.rfl

/-- **A character and a weight of different parities admit only the zero form.** If $f$ is a
modular form of type $(k, \varepsilon)$ on $\Gamma_0(N)$ and $\varepsilon(-1) \ne (-1)^k$, then
$f = 0$: the transformation law for $-1 \in \Gamma_0(N)$ reads
$f = \varepsilon(-1)(-1)^k f$.

Source: P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4)
7 (1974), 507–530, §1.5, p. 509 ("si ε et k n'étaient pas de même parité, cette formule
entraînerait f = 0"). -/
theorem HasNebentypus.eq_zero_of_ne {ε : DirichletCharacter ℂ N} {f : ModularForm (Gamma1 N) k}
    (hf : HasNebentypus ε f) (hε : ε (-1) ≠ (-1) ^ k) : f = 0 := by
  have hmem : (-1 : SL(2, ℤ)) ∈ Gamma0 N := by
    rw [Gamma0_mem]
    simp
  have hk : ((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ k) = 1 := by
    rw [← mul_zpow, neg_one_mul, neg_neg, one_zpow]
  have hprod : ε (-1) * (-1 : ℂ) ^ k ≠ 1 := by
    intro h
    apply hε
    calc ε (-1) = ε (-1) * ((-1 : ℂ) ^ k * (-1 : ℂ) ^ k) := by rw [hk, mul_one]
      _ = (ε (-1) * (-1 : ℂ) ^ k) * (-1 : ℂ) ^ k := by ring
      _ = (-1) ^ k := by rw [h, one_mul]
  ext τ
  have h := hf (-1) hmem τ
  have hτ : (-1 : SL(2, ℤ)) • τ = τ := by simp
  rw [hτ] at h
  have h' : f τ = (ε (-1) * (-1 : ℂ) ^ k) * f τ := by
    convert h using 1
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_apply, Matrix.one_apply_eq]
    simp [mul_assoc]
  have : (1 - ε (-1) * (-1 : ℂ) ^ k) * f τ = 0 := by
    rw [sub_mul, one_mul, ← h', sub_self]
  simpa [sub_eq_zero, Ne.symm hprod] using this

/-- **Eigenvectors of the Hecke operators `T_p`, `p ∤ N`, on forms of type `(k, ε)`.** For a
prime $p \nmid N$ and a modular form $f = \sum_{n \ge 0} c_n q^n$ of type $(k, \varepsilon)$ on
$\Gamma_0(N)$, Deligne and Serre's formula (1.6.1) is
$$f|T_p = \sum_{n \ge 0} c_{pn} q^n + \varepsilon(p)\, p^{k-1} \sum_{n \ge 0} c_n q^{pn}.$$
The form $f$ is an eigenvector of the $T_p$, $p \nmid N$, with eigenvalues $a_p$ if $f \ne 0$ and
$f|T_p = a_p f$ for every prime $p \nmid N$, that is,
$$c_{pn} + \varepsilon(p)\, p^{k-1} c_{n/p} = a_p c_n \qquad \text{for every } n \ge 0,$$
where $c_{n/p} = 0$ when $p \nmid n$. Here $c_n$ is `ModularFormClass.qCoeff f n`, the
coefficient of $q^n$, $q = e^{2\pi i z}$. The definition does not ask $f$ to have type
$(k, \varepsilon)$; Deligne and Serre apply it to forms of that type.

Source: P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4)
7 (1974), 507–530, §1.6, formula (1.6.1), p. 509; the eigenvectors of their Théorème 4.1, p. 513,
and Proposition 5.1, p. 518, are forms that are not identically zero. -/
def IsHeckeEigenvector (ε : DirichletCharacter ℂ N) (f : ModularForm (Gamma1 N) k)
    (a : ℕ → ℂ) : Prop :=
  f ≠ 0 ∧ ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
    qCoeff f (p * n) + ε (p : ZMod N) * (p : ℂ) ^ (k - 1) *
        (if p ∣ n then qCoeff f (n / p) else 0) =
      a p * qCoeff f n

end ModularForm

end
