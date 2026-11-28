# Uniform bound on the images of the representations modulo ℓ

Keep the notation of
[Representations modulo ℓ attached to a weight-one cuspidal eigenform](representations-mod-l-of-a-weight-one-cuspidal-eigenform.md):
a cusp form $f \ne 0$ of type $(1, \varepsilon)$ on $\Gamma_0(N)$, an eigenvector of the $T_p$, $p \nmid N$, with eigenvalues
$a_p$, the number field $K$, the set $L$ of primes that split completely in $K$, and for each $\ell \in L$ a
representation $\rho_\ell \colon \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to \mathrm{GL}_2(\mathbb{F}_\ell)$ as there. Let
$G_\ell \subseteq \mathrm{GL}_2(\mathbb{F}_\ell)$ be the image of $\rho_\ell$. Then there is a constant $A$ such that

$$|G_\ell| \le A \qquad \text{for every } \ell \in L.$$

This is Lemme 8.4 of Deligne–Serre, which they derive from Lemme 8.3 and Proposition 7.2.

Proof. Lemme 8.3: for every $\eta > 0$ there is a constant $M$ such that $G_\ell$ satisfies the condition $C(\eta, M)$ of
[the bound on semisimple subgroups](bounded-semisimple-subgroups-of-gl2-with-few-characteristic-polynomials.md) for every
$\ell \in L$. Indeed, take $X_\eta$ as in
[the weight-one finiteness statement](weight-one-eigenvalues-are-finitely-many-outside-a-sparse-set.md), so that
$\operatorname{dens.sup} X_\eta \le \eta$ and the $a_p$, $p \nmid N$, $p \notin X_\eta$, form a finite set; let $\mathcal{M}$ be
the finite set of the polynomials $1 - a_p T + \varepsilon(p) T^2$ for these $p$, and $M = |\mathcal{M}|$. For $\ell \in L$ let
$H_\ell$ be the set of the Frobenius elements $F_{\rho_\ell,p}$, $p \notin X_\eta$, $p \nmid N\ell$, and of their conjugates.
By the [Chebotarev density theorem](../../adeles-class-field-theory/chebotarev-density-theorem.md), applied to the finite
Galois extension of $\mathbb{Q}$ cut out by $\rho_\ell$, the primes whose Frobenius elements lie in the conjugation-stable set
$G_\ell \smallsetminus H_\ell$ have Dirichlet density $|G_\ell \smallsetminus H_\ell|/|G_\ell|$; all but finitely many of them lie in
$X_\eta$, so this density is at most $\eta$ and $|H_\ell| \ge (1 - \eta)|G_\ell|$. For $h \in H_\ell$, $\det(1 - hT)$ is the
reduction modulo $\lambda_\ell$ of an element of $\mathcal{M}$, so these polynomials form a set of at most $M$ elements.
Lemme 8.4: take $\eta < 1/2$ in Lemme 8.3; each $G_\ell$ is a semisimple subgroup of $\mathrm{GL}_2(\mathbb{F}_\ell)$, since
$\rho_\ell$ is semisimple, so $|G_\ell| \le A(\eta, M)$.

## Depends on

- [Modular forms of type (k, ε) on Γ₀(N)](modular-forms-of-type-k-epsilon.md), for cusp forms of type $(1, \varepsilon)$ and the operators $T_p$
- [Representations modulo ℓ attached to a weight-one cuspidal eigenform](representations-mod-l-of-a-weight-one-cuspidal-eigenform.md), for $\rho_\ell$

## Proof depends on

- [Representations modulo ℓ attached to a weight-one cuspidal eigenform](representations-mod-l-of-a-weight-one-cuspidal-eigenform.md), for the semisimplicity of $\rho_\ell$ and its Frobenius polynomials modulo $\lambda_\ell$
- [Eigenvalues of a weight-one cusp form take finitely many values outside a set of small upper density](weight-one-eigenvalues-are-finitely-many-outside-a-sparse-set.md), for $X_\eta$ (Lemme 8.3)
- [Chebotarev density theorem](../../adeles-class-field-theory/chebotarev-density-theorem.md), for $|H_\ell| \ge (1 - \eta)|G_\ell|$ (Lemme 8.3)
- [Bounded order of semisimple subgroups of GL₂(F_ℓ) with few characteristic polynomials](bounded-semisimple-subgroups-of-gl2-with-few-characteristic-polynomials.md), for the constant $A(\eta, M)$

## Sources

- P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7 (1974), 507–530,
  [doi:10.24033/asens.1277](https://doi.org/10.24033/asens.1277): Lemme 8.3 and its proof, p. 525 ("Pour tout η > 0, il
  existe une constante M telle que $G_l$ satisfasse à la condition C(η, M) de 7.1 pour tout l ∈ L"); Lemme 8.4, p. 525
  ("Il existe une constante A telle que $|G_l| \leqq A$ pour tout l ∈ L. Cela résulte du lemme précédent, et de la
  proposition 7.2").
