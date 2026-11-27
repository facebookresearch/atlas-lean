# Rankin's bound for the mean square of Hecke eigenvalues

Let $N \ge 1$, let $\varepsilon$ be a Dirichlet character mod $N$ and $k \ge 1$ an integer with
$\varepsilon(-1) = (-1)^k$, and let $f \ne 0$ be a cusp form of
[type $(k, \varepsilon)$ on $\Gamma_0(N)$](modular-forms-of-type-k-epsilon.md) that is an eigenvector of the Hecke
operators $T_p$, $p \nmid N$, with eigenvalues $a_p$. Then the series $\sum_{p \nmid N} |a_p|^2 p^{-s}$, over the primes
not dividing $N$, converges for every real $s > k$, and

$$\sum_{p \nmid N} |a_p|^2 p^{-s} \le \log\bigl(1/(s-k)\bigr) + O(1)$$

as the real number $s$ tends to $k$ from above.

Deligne and Serre first replace $f$ by a primitive form, in one sentence ("On se ramène aussitôt au cas où f est une
forme primitive"), and then write $N$ for its level. In detail: by the decomposition of §1.9 there are a divisor $M$ of
$N$ such that $\varepsilon$ can be defined mod $M$, that is, $\varepsilon(d) = \varepsilon_M(d \bmod M)$ for a Dirichlet
character $\varepsilon_M$ mod $M$, and a primitive cusp form $f_0 = \sum_{n \ge 1} b_n q^n$ of type
$(k, \varepsilon_M)$ on $\Gamma_0(M)$, with $b_1 = 1$, such that $b_p = a_p$ for every prime $p \nmid N$. The level $M$
may be a proper divisor of $N$; the formulas below are those of $f_0$ at its own level $M$, so that (1.7.2) has linear
factors only at the primes dividing $M$. For $p \nmid M$ choose $\varphi_p \in \mathrm{GL}_2(\mathbb{C})$ with
$\operatorname{Tr}(\varphi_p) = b_p$ and $\det(\varphi_p) = \varepsilon_M(p) p^{k-1}$, so that by (1.7.2)

$$\sum_{n \ge 1} b_n n^{-s} = \prod_{p \mid M} (1 - b_p p^{-s})^{-1} \prod_{p \nmid M} \det(1 - \varphi_p p^{-s})^{-1},$$

and compare

$$L(s) = \prod_{p \nmid M} \det(1 - \varphi_p \otimes \overline{\varphi}_p\, p^{-s})^{-1} = H(s)\, \zeta(2s - 2k + 2) \sum_{n \ge 1} |b_n|^2 n^{-s},
\qquad H(s) = \prod_{p \mid M} (1 - p^{-2s + 2k - 2})(1 - |b_p|^2 p^{-s}),$$

with the [Rankin–Selberg series](rankin-selberg-series-of-a-primitive-form.md) of $f_0$. Since $|b_p| < p^{k/2}$ for
$p \mid M$ (§1.8, for $f_0$ at level $M$), $H$ is holomorphic and nonzero on $\operatorname{Re}(s) \ge k$, so $L$ is
holomorphic there except for a simple pole at $s = k$, and nonzero for real $s > k$. The Dirichlet series
$g(s) = \sum_{m \ge 1} \sum_{p \nmid M} |\operatorname{Tr}(\varphi_p^m)|^2 p^{-ms}/m$ has nonnegative coefficients and
equals $\log L(s)$ for large real $s$; by Landau's lemma it converges for $\operatorname{Re}(s) > k$, and
$g(s) = \log(1/(s-k)) + O(1)$ as $s \to k$. Its terms with $m = 1$ give
$\sum_{p \nmid M} |b_p|^2 p^{-s} \le \log(1/(s-k)) + O(1)$. The series of the statement is this one without the terms
of the finitely many primes that divide $N$ but not $M$, which are nonnegative and bounded for real $s$ near $k$; so
it converges for real $s > k$ and satisfies the same bound.

## Depends on

- [Modular forms of type (k, ε) on Γ₀(N)](modular-forms-of-type-k-epsilon.md), for cusp forms of type $(k, \varepsilon)$ and the operators $T_p$

## Proof depends on

- [Rankin–Selberg series of a primitive form](rankin-selberg-series-of-a-primitive-form.md), applied to $f_0$ at level $M$, for the continuation of $\zeta(2s-2k+2)\sum |b_n|^2 n^{-s}$ to $\operatorname{Re}(s) > k - 1$, holomorphic there except for a simple pole at $s = k$
- [Landau's theorem on Dirichlet series with non-negative coefficients](../../../zeta-l-functions/dirichlet-l-functions/analytic-continuation-of-dirichlet-series/landau-theorem-dirichlet-series.md), for the convergence of $g(s)$ on $\operatorname{Re}(s) > k$ (Landau's lemma, [21], p. 112, as cited by Deligne–Serre)

## Expansion

This node is still to be broken down. A good expansion states and links:

- the decomposition of §1.9 of a form of type $(k, \varepsilon)$ on $\Gamma_0(N)$ into an Eisenstein series and the forms
  $f_i(d_i z)$, for primitive cusp forms $f_i$ of type $(k, \varepsilon)$ on $\Gamma_0(N_i)$, $N_i$ a divisor of $N$ such
  that $\varepsilon$ can be defined mod $N_i$ and $d_i$ a divisor of $N/N_i$, and the consequence that a cusp form that
  is an eigenvector of the $T_p$, $p \nmid N$, has the eigenvalues $a_p$, $p \nmid N$, of a primitive form of some level
  $M$ dividing $N$;
- the Euler product (1.7.2) of a primitive form of level $M$, from its being an eigenvector of the $T_p$, $p \nmid M$,
  and the $U_p$, $p \mid M$, with $b_1 = 1$ (§1.7);
- the absolute values of the coefficients $b_p$, $p \mid M$, of a primitive form of level $M$ (§1.8, citing Li [12] and
  Ogg [14], as cited there), which give $|b_p| < p^{k/2}$;
- the identity $L(s) = H(s)\,\zeta(2s - 2k + 2) \sum |b_n|^2 n^{-s}$, which Deligne–Serre derive from
  $\lambda_p \overline{\lambda}_p \mu_p \overline{\mu}_p = p^{2k-2}$ for the eigenvalues $\lambda_p, \mu_p$ of $\varphi_p$ (citing
  Jacquet [10], p. 33, Li [12] and Ogg [15], as cited there).

## Sources

- P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7 (1974), 507–530,
  [doi:10.24033/asens.1277](https://doi.org/10.24033/asens.1277): Proposition 5.1 and (5.1.1), p. 518 ("Soit f une forme
  modulaire parabolique de type (k, ε) sur Γ₀(N), non identiquement nulle. On suppose que f est fonction propre des
  $T_p$, $p \nmid N$, avec pour valeurs propres $a_p$"), and Démonstration 5.2, pp. 518–519; §1.5, p. 509, for forms of
  type $(k, \varepsilon)$; (1.6.1), p. 509, for $T_p$; §1.7 and (1.7.2), p. 509; §1.8, pp. 509–510; §1.9, p. 510, for
  the decomposition into primitive forms of levels $N_i$ dividing $N$.
- J.-P. Serre, *Cours d'arithmétique*, Presses Universitaires de France, Paris (1970), p. 112, for Landau's lemma, as
  cited in Deligne–Serre (1974), p. 519; not read.
