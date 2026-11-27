# Eigenvalues of a weight-one cusp form take finitely many values outside a set of small upper density

For a set $X$ of primes, its upper density is

$$\operatorname{dens.sup} X = \limsup_{s \to 1,\ s > 1} \Bigl( \sum_{p \in X} p^{-s} \Bigr) \Big/ \log\bigl(1/(s-1)\bigr),$$

the limit superior over real $s > 1$; it lies between $0$ and $1$.

Let $N \ge 1$, let $\varepsilon$ be a Dirichlet character mod $N$ with $\varepsilon(-1) = -1$, and let $f \ne 0$ be a cusp
form of [type $(1, \varepsilon)$ on $\Gamma_0(N)$](modular-forms-of-type-k-epsilon.md) that is an eigenvector of the
Hecke operators $T_p$, $p \nmid N$, with eigenvalues $a_p$. Then for every $\eta > 0$ there are a set $X_\eta$ of
primes and a finite subset $Y_\eta$ of $\mathbb{C}$ such that

$$\operatorname{dens.sup} X_\eta \le \eta \qquad \text{and} \qquad a_p \in Y_\eta \text{ for every prime } p \nmid N \text{ with } p \notin X_\eta.$$

Deligne and Serre write the last condition for all $p \notin X_\eta$, the eigenvalues being defined for $p \nmid N$ only.

Proof (Deligne–Serre, p. 520). By the
[integral lattice of cusp forms](integral-lattice-of-cusp-forms-and-algebraicity-of-hecke-eigenvalues.md) (parts 3
and 4) the $a_p$ are algebraic integers of a number field $K$, of degree $r$ over $\mathbb{Q}$, and for every embedding
$\sigma$ of $K$ into $\mathbb{C}$, extended to an automorphism of $\mathbb{C}$, the numbers $\sigma(a_p)$ are the eigenvalues
of the $T_p$ on the cusp form $\sigma(f) \ne 0$ of type $(1, \sigma \circ \varepsilon)$. For $c \ge 0$ let $Y(c)$ be the set
of algebraic integers $a$ of $K$ with $|\sigma(a)|^2 \le c$ for every embedding $\sigma$; it is finite, since the minimal
polynomials of its elements are monic of degree at most $r$ with integer coefficients bounded in terms of $c$ and $r$.
Let $X(c)$ be the set of primes $p \nmid N$ with $a_p \notin Y(c)$. Summing (5.1.1) of
[Rankin's bound](rankin-bound-for-the-mean-square-of-hecke-eigenvalues.md) over the $r$ forms $\sigma(f)$ gives

$$\sum_\sigma \sum_{p \nmid N} |\sigma(a_p)|^2 p^{-s} \le r \log\bigl(1/(s-1)\bigr) + O(1) \qquad (s \to 1),$$

and $\sum_\sigma |\sigma(a_p)|^2 \ge c$ for $p \in X(c)$, so $c \sum_{p \in X(c)} p^{-s} \le r \log(1/(s-1)) + O(1)$ and
$\operatorname{dens.sup} X(c) \le r/c$. Take $c \ge r/\eta$, $X_\eta = X(c)$ and $Y_\eta = Y(c)$.

## Depends on

- [Modular forms of type (k, ε) on Γ₀(N)](modular-forms-of-type-k-epsilon.md), for cusp forms of type $(1, \varepsilon)$ and the operators $T_p$

## Proof depends on

- [Integral lattice of cusp forms on Γ₁(N) and algebraicity of their Hecke eigenvalues](integral-lattice-of-cusp-forms-and-algebraicity-of-hecke-eigenvalues.md), for the number field $K$ containing the $a_p$ and for the conjugate eigenforms $\sigma(f)$
- [Rankin's bound for the mean square of Hecke eigenvalues](rankin-bound-for-the-mean-square-of-hecke-eigenvalues.md), applied to each $\sigma(f)$ in weight $k = 1$

## Sources

- P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7 (1974), 507–530,
  [doi:10.24033/asens.1277](https://doi.org/10.24033/asens.1277): §5.4 and (5.4.1), p. 519; Proposition 5.5, pp. 519–520
  ("On conserve les hypothèses de 5.1, et l'on suppose en outre que le poids k de f est égal à 1. Alors, pour tout
  η > 0, il existe un ensemble $X_\eta$ de nombres premiers et une partie finie $Y_\eta$ de $\mathbf{C}$ tels que
  dens. sup $X_\eta \leqq \eta$ et $a_p \in Y_\eta$ pour tout $p \notin X_\eta$"), and its proof, p. 520; Remarque 5.6,
  p. 520.
