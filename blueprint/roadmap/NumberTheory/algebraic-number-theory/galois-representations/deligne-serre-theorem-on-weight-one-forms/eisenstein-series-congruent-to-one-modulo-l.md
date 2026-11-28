# Eisenstein series congruent to 1 modulo ℓ

Let $\ell$ be a prime and $n > 2$ an even integer divisible by $\ell - 1$, and let $E_n$ be the Eisenstein series of
weight $n$ on $\mathrm{SL}_2(\mathbb{Z})$ normalized so that its constant term is $1$. Then the $q$-expansion of $E_n$ is
$\ell$-integral, its coefficients being rational numbers with denominators prime to $\ell$, and

$$E_n \equiv 1 \pmod{\ell},$$

that is, every coefficient of $E_n - 1$ has positive $\ell$-adic valuation.

Consequently, if $K \subset \mathbb{C}$ is a number field, $\lambda$ a finite place of $K$ above $\ell$, and $f$ a
[modular form of type $(k, \varepsilon)$ on $\Gamma_0(N)$](modular-forms-of-type-k-epsilon.md) whose $q$-expansion
coefficients lie in the valuation ring $\mathcal{O}_\lambda$ of $\lambda$, then $f \cdot E_n$ is a modular form of type
$(k + n, \varepsilon)$ on $\Gamma_0(N)$ with coefficients in $\mathcal{O}_\lambda$, congruent to $f$ modulo $\lambda$
coefficient by coefficient, and its weight satisfies $k + n \equiv k \pmod{\ell - 1}$.

This is the step 6.9 of Deligne–Serre's proof of
[the representations modulo λ attached to eigenforms modulo λ](representations-mod-lambda-of-eigenforms-mod-lambda.md),
which brings a form of weight $1$ to weight $1 + n \ge 2$ without changing it modulo $\lambda$ or changing $k$ modulo
$\ell - 1$; they cite Swinnerton-Dyer for the congruence $E_n \equiv 1 \pmod{\ell}$.

Proof. Write $E_n = \sum_{m \ge 0} c_m q^m$. The first assertion, on the coefficients of $E_n$, is stated for the
normalized Eisenstein series `ModularForm.E` of weight $n$ by two declarations: Mathlib's
`EisensteinSeries.E_qExpansion_coeff_zero` gives $c_0 = 1$, and `ModularForm.eisenstein_qCoeff_p_integral_dvd`, for the
prime $\ell$, gives for every $m \ge 1$ integers $x$ and $s$ with $\ell \mid x$, $\ell \nmid s$ and $s c_m = x$, so
that $c_m = x/s \in \ell\mathbb{Z}_{(\ell)}$. (Classically, $c_m = -(2n/B_n)\,\sigma_{n-1}(m)$ for $m \ge 1$, with
$B_n$ the Bernoulli number, and for $\ell - 1 \mid n$ the
[Von Staudt–Clausen theorem](../../../special-numbers/bernoulli-numbers/identities-for-bernoulli-numbers/von-staudt-clausen.md)
gives $\ell B_n \equiv -1 \pmod{\ell}$, hence $2n/B_n \in \ell\mathbb{Z}_{(\ell)}$.) The second assertion follows by
multiplying $q$-expansions. Since $E_n|_n\gamma = E_n$ for every $\gamma \in \mathrm{SL}_2(\mathbb{Z})$, the product
$f \cdot E_n$ satisfies the transformation law of type $(k + n, \varepsilon)$, and $\varepsilon(-1) = (-1)^{k+n}$ as $n$
is even; it is holomorphic on the upper half-plane and at the cusps, since $f$ and $E_n$ are. Its $q$-expansion is the
product of those of $f = \sum_{i \ge 0} a_i q^i$ and $E_n$, with $m$-th coefficient
$\sum_{i + j = m} a_i c_j = a_m + \sum_{j = 1}^{m} a_{m-j} c_j$. As $\mathbb{Z}_{(\ell)} \subseteq \mathcal{O}_\lambda$ and
$\ell \in \mathfrak{m}_\lambda$, the maximal ideal of $\mathcal{O}_\lambda$, each $c_j$ with $j \ge 1$ lies in
$\mathfrak{m}_\lambda$, so this coefficient lies in $\mathcal{O}_\lambda$ and is congruent to $a_m$ modulo $\lambda$.
Finally $k + n \equiv k \pmod{\ell - 1}$ since $\ell - 1 \mid n$.

## Depends on

- [Modular forms of type (k, ε) on Γ₀(N)](modular-forms-of-type-k-epsilon.md), for the forms $f$ and $f \cdot E_n$ of types $(k, \varepsilon)$ and $(k + n, \varepsilon)$

## Proof depends on

- [Von Staudt–Clausen theorem](../../../special-numbers/bernoulli-numbers/identities-for-bernoulli-numbers/von-staudt-clausen.md), for $\ell B_n \equiv -1 \pmod{\ell}$ in the classical proof of the first assertion from the Bernoulli-number formula for the $c_m$

## Expansion

This node is still to be broken down. A good expansion states and links:

- the first assertion, which `ModularForm.eisenstein_qCoeff_p_integral_dvd` (the coefficients $c_m$, $m \ge 1$) and
  Mathlib's `EisensteinSeries.E_qExpansion_coeff_zero` (the constant term $c_0 = 1$) state for `ModularForm.E`;
- the product of a modular form of type $(k, \varepsilon)$ on $\Gamma_0(N)$ and a modular form of weight $n$ on
  $\mathrm{SL}_2(\mathbb{Z})$: a modular form of type $(k + n, \varepsilon)$ on $\Gamma_0(N)$, whose $q$-expansion is the
  product of their $q$-expansions, which with the first assertion gives the congruence $f \cdot E_n \equiv f$
  (mod $\lambda$).

## Sources

- P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7 (1974), 507–530,
  [doi:10.24033/asens.1277](https://doi.org/10.24033/asens.1277): §6.9, p. 522 ("Pour n pair > 2, soit $E_n$ la série
  d'Eisenstein de poids n sur $\mathbf{SL}_2(\mathbf{Z})$ normalisée pour que son terme constant soit 1. Si l'on choisit n
  divisible par l − 1, le développement en série de $E_n$ est l-entier, et $E_n \equiv 1$ (mod l), cf. [25]. Le produit
  $f.E_n$ est donc congru à f mod λ; son poids k + n est congru à k mod (l − 1)"); §6.6, p. 521, for λ-integral forms
  and congruences modulo λ.
- H. P. F. Swinnerton-Dyer, *On l-adic representations and congruences for coefficients of modular forms*, Lecture
  Notes in Math. 350, Springer (1973), 1–55, as cited in Deligne–Serre (1974), p. 522; not read.
