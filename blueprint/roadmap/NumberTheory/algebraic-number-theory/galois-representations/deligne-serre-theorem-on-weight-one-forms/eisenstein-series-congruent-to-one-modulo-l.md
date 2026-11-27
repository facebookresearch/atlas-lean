# Eisenstein series congruent to 1 modulo ℓ

Let $\ell$ be a prime and $n > 2$ an even integer divisible by $\ell - 1$, and let $E_n$ be the Eisenstein series of
weight $n$ on $\mathrm{SL}_2(\mathbb{Z})$ normalized so that its constant term is $1$. Then the $q$-expansion of $E_n$ is
$\ell$-integral, its coefficients being rational numbers with denominators prime to $\ell$, and

$$E_n \equiv 1 \pmod{\ell},$$

that is, every coefficient of $E_n - 1$ has positive $\ell$-adic valuation.

Consequently, if $K \subset \mathbb{C}$ is a number field, $\lambda$ a finite place of $K$ above $\ell$, and $f$ a modular
form of type $(k, \varepsilon)$ on $\Gamma_0(N)$ (as on
[Rankin's bound](rankin-bound-for-the-mean-square-of-hecke-eigenvalues.md)) whose $q$-expansion coefficients lie in the
valuation ring $\mathcal{O}_\lambda$ of $\lambda$, then $f \cdot E_n$ is a modular form of type $(k + n, \varepsilon)$ on
$\Gamma_0(N)$ with coefficients in $\mathcal{O}_\lambda$, congruent to $f$ modulo $\lambda$ coefficient by coefficient, and its
weight satisfies $k + n \equiv k \pmod{\ell - 1}$.

This is the step 6.9 of Deligne–Serre's proof of
[the representations modulo λ attached to eigenforms modulo λ](representations-mod-lambda-of-eigenforms-mod-lambda.md),
which brings a form of weight $1$ to weight $1 + n \ge 2$ without changing it modulo $\lambda$ or changing $k$ modulo
$\ell - 1$; they cite Swinnerton-Dyer for the congruence $E_n \equiv 1 \pmod{\ell}$.

## Proof depends on

Its proof uses the inputs listed under Expansion.

## Expansion

This node is still to be broken down. A good expansion states and links:

- the $q$-expansion of $E_n$, whose coefficients are $1$ and the numbers $-(2n/B_n)\,\sigma_{n-1}(m)$, $m \ge 1$, with
  $B_n$ the Bernoulli number;
- the [Von Staudt–Clausen theorem](../../../special-numbers/bernoulli-numbers/identities-for-bernoulli-numbers/von-staudt-clausen.md),
  which for $\ell - 1 \mid n$ gives $\ell B_n \equiv -1 \pmod{\ell}$, hence $2n/B_n \equiv 0 \pmod{\ell}$; Deligne–Serre cite
  Swinnerton-Dyer [25] for the congruence (as cited in Deligne–Serre (1974), p. 522);
- the transformation law and $q$-expansion of a product of modular forms, for $f \cdot E_n$.

## Sources

- P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7 (1974), 507–530,
  [doi:10.24033/asens.1277](https://doi.org/10.24033/asens.1277): §6.9, p. 522 ("Pour n pair > 2, soit $E_n$ la série
  d'Eisenstein de poids n sur $\mathbf{SL}_2(\mathbf{Z})$ normalisée pour que son terme constant soit 1. Si l'on choisit n
  divisible par l − 1, le développement en série de $E_n$ est l-entier, et $E_n \equiv 1$ (mod l), cf. [25]. Le produit
  $f.E_n$ est donc congru à f mod λ; son poids k + n est congru à k mod (l − 1)"); §6.6, p. 521, for λ-integral forms
  and congruences modulo λ.
- H. P. F. Swinnerton-Dyer, *On l-adic representations and congruences for coefficients of modular forms*, Lecture
  Notes in Math. 350, Springer (1973), 1–55, as cited in Deligne–Serre (1974), p. 522; not read.
