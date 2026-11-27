# Representations modulo ℓ attached to a weight-one cuspidal eigenform

Let $N \ge 1$, let $\varepsilon$ be a Dirichlet character mod $N$ with $\varepsilon(-1) = -1$, and let $f \ne 0$ be a cusp
form of [type $(1, \varepsilon)$ on $\Gamma_0(N)$](modular-forms-of-type-k-epsilon.md) that is an eigenvector of the
Hecke operators $T_p$, $p \nmid N$, with eigenvalues $a_p$. Let $K \subset \mathbb{C}$ be a number field, Galois over
$\mathbb{Q}$, whose ring of integers $\mathcal{O}_K$ contains the $a_p$ and the $\varepsilon(p)$; such a field exists by the
[integral lattice of cusp forms](integral-lattice-of-cusp-forms-and-algebraicity-of-hecke-eigenvalues.md). Let $L$ be the
set of primes $\ell$ that split completely in $K$, and for each $\ell \in L$ choose a place $\lambda_\ell$ of $K$ above
$\ell$, whose residue field is $\mathbb{F}_\ell$. Then for each $\ell \in L$ there is a continuous semisimple representation

$$\rho_\ell \colon \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to \mathrm{GL}_2(\mathbb{F}_\ell),$$

unramified outside $N\ell$, such that

$$\det(1 - F_{\rho_\ell,p} T) \equiv 1 - a_p T + \varepsilon(p) T^2 \pmod{\lambda_\ell} \qquad \text{for every prime } p \nmid N\ell,$$

with unramified and $F_{\rho_\ell,p}$ as on
[Semisimple Galois representations with the same Frobenius polynomials](semisimple-galois-representations-with-equal-frobenius-polynomials.md).

This is §8.2 of Deligne–Serre, who deduce it from Théorème 6.7. In detail: by parts 1 and 2 of the
[integral lattice of cusp forms](integral-lattice-of-cusp-forms-and-algebraicity-of-hecke-eigenvalues.md), the cusp forms
$g$ of weight $1$ on $\Gamma_1(N)$ with $g|R_d = \varepsilon(d) g$ and $g|T_p = a_p g$ for all $d$ and all $p \nmid N$ form
the solutions of linear conditions with coefficients in $K$ on the space of forms with coefficients in $K$, extended
to $\mathbb{C}$; as $f \ne 0$ is one of them, there is such a nonzero form $f'$ with coefficients in $K$, and after
multiplying by an element of $K$, $f'$ is $\lambda_\ell$-integral with $f' \not\equiv 0$ (mod $\lambda_\ell$). Then $f'$ is an
eigenvector of the $T_p$ modulo $\lambda_\ell$ with eigenvalues the reductions of the $a_p$, which lie in $\mathbb{F}_\ell$, and
[the representations modulo λ](representations-mod-lambda-of-eigenforms-mod-lambda.md), with $k = 1$, give
$\rho_\ell$ with values in $\mathrm{GL}_2(k_{f'}) \subseteq \mathrm{GL}_2(\mathbb{F}_\ell)$, trace $a_p$ and determinant $\varepsilon(p)$ modulo
$\lambda_\ell$ at $F_{\rho_\ell,p}$, which is the congruence above.

## Depends on

- [Modular forms of type (k, ε) on Γ₀(N)](modular-forms-of-type-k-epsilon.md), for cusp forms of type $(1, \varepsilon)$ and the operators $T_p$
- [Semisimple Galois representations with the same Frobenius polynomials are isomorphic](semisimple-galois-representations-with-equal-frobenius-polynomials.md), for the conventions on unramified representations and Frobenius elements

## Proof depends on

- [Integral lattice of cusp forms on Γ₁(N) and algebraicity of their Hecke eigenvalues](integral-lattice-of-cusp-forms-and-algebraicity-of-hecke-eigenvalues.md), for the field $K$ and for an eigenform with coefficients in $K$
- [Representations modulo λ attached to eigenforms modulo λ](representations-mod-lambda-of-eigenforms-mod-lambda.md), applied in weight $1$ at the place $\lambda_\ell$

## Sources

- P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7 (1974), 507–530,
  [doi:10.24033/asens.1277](https://doi.org/10.24033/asens.1277): §8.2, p. 525 ("D'après 2.7, les $a_p$ et les ε(p)
  appartiennent à l'anneau des entiers $\mathfrak{O}_K$ d'un corps de nombres K, que l'on peut supposer galoisien sur
  $\mathbf{Q}$. Soit L l'ensemble des nombres premiers l qui se décomposent complètement dans K. […] D'après le
  théorème 6.7, il existe une représentation semi-simple continue"), with the congruence for $p \nmid Nl$.
