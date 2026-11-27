# Rankin's bound for the mean square of Hecke eigenvalues

Let $N \ge 1$, let $\varepsilon$ be a Dirichlet character mod $N$ and $k \ge 1$ an integer with
$\varepsilon(-1) = (-1)^k$. A modular form of type $(k, \varepsilon)$ on $\Gamma_0(N)$ is a modular form $f$ of weight $k$
on $\Gamma_1(N)$ with

$$f\left(\frac{az+b}{cz+d}\right) = \varepsilon(d)\,(cz+d)^k f(z) \qquad \text{for all } \begin{pmatrix} a & b \\ c & d \end{pmatrix} \in \Gamma_0(N),$$

and for a prime $p \nmid N$ the Hecke operator $T_p$ acts on it by
$f|T_p = \sum_n a_{pn} q^n + \varepsilon(p) p^{k-1} \sum_n a_n q^{pn}$, where $f = \sum_n a_n q^n$, $q = e^{2\pi i z}$.

Let $f \ne 0$ be a cusp form of type $(k, \varepsilon)$ on $\Gamma_0(N)$ that is an eigenvector of the $T_p$, $p \nmid N$,
with eigenvalues $a_p$. Then the series $\sum_{p \nmid N} |a_p|^2 p^{-s}$, over the primes not dividing $N$, converges
for every real $s > k$, and

$$\sum_{p \nmid N} |a_p|^2 p^{-s} \le \log\bigl(1/(s-k)\bigr) + O(1)$$

as the real number $s$ tends to $k$ from above.

Deligne and Serre first replace $f$ by a primitive form $\sum a_n q^n$ with the same eigenvalues (§1.9). For
$p \nmid N$ they choose $\varphi_p \in \mathrm{GL}_2(\mathbb{C})$ with $\operatorname{Tr}(\varphi_p) = a_p$ and
$\det(\varphi_p) = \varepsilon(p) p^{k-1}$, so that by (1.7.2)

$$\sum_{n \ge 1} a_n n^{-s} = \prod_{p \mid N} (1 - a_p p^{-s})^{-1} \prod_{p \nmid N} \det(1 - \varphi_p p^{-s})^{-1},$$

and they compare

$$L(s) = \prod_{p \nmid N} \det(1 - \varphi_p \otimes \overline{\varphi}_p\, p^{-s})^{-1} = H(s)\, \zeta(2s - 2k + 2) \sum_{n \ge 1} |a_n|^2 n^{-s},
\qquad H(s) = \prod_{p \mid N} (1 - p^{-2s + 2k - 2})(1 - |a_p|^2 p^{-s}),$$

with the [Rankin–Selberg series](rankin-selberg-series-of-a-primitive-form.md). Since $|a_p| < p^{k/2}$ for $p \mid N$
(§1.8), $H$ is holomorphic and nonzero on $\operatorname{Re}(s) \ge k$, so $L$ is holomorphic there except for a simple pole
at $s = k$, and nonzero for real $s > k$. The Dirichlet series
$g(s) = \sum_{m \ge 1} \sum_{p \nmid N} |\operatorname{Tr}(\varphi_p^m)|^2 p^{-ms}/m$ has nonnegative coefficients and equals
$\log L(s)$ for large real $s$; by Landau's lemma it converges for $\operatorname{Re}(s) > k$, and
$g(s) = \log(1/(s-k)) + O(1)$ as $s \to k$. Its terms with $m = 1$ give the bound.

## Proof depends on

- [Rankin–Selberg series of a primitive form](rankin-selberg-series-of-a-primitive-form.md), for the continuation of $\zeta(2s-2k+2)\sum |a_n|^2 n^{-s}$ with its only pole, simple, at $s = k$
- [Landau's theorem on Dirichlet series with non-negative coefficients](../../../zeta-l-functions/dirichlet-l-functions/analytic-continuation-of-dirichlet-series/landau-theorem-dirichlet-series.md), for the convergence of $g(s)$ on $\operatorname{Re}(s) > k$ (Landau's lemma, [21], p. 112, as cited by Deligne–Serre)

## Expansion

This node is still to be broken down. A good expansion states and links:

- the decomposition of §1.9 of a form of type $(k, \varepsilon)$ into an Eisenstein series and the forms $f_i(d_i z)$ for
  primitive forms $f_i$ of levels dividing $N$, and the consequence that a cusp form that is an eigenvector of the
  $T_p$, $p \nmid N$, has the eigenvalues of a primitive form;
- the Euler product (1.7.2) of a primitive form, from its being an eigenvector of the $T_p$ and $U_p$ with $a_1 = 1$
  (§1.7);
- the absolute values of the $a_p$ for $p \mid N$ (§1.8, citing Li [12] and Ogg [14], as cited there), which give
  $|a_p| < p^{k/2}$;
- the identity $L(s) = H(s)\,\zeta(2s - 2k + 2) \sum |a_n|^2 n^{-s}$, which Deligne–Serre derive from
  $\lambda_p \overline{\lambda}_p \mu_p \overline{\mu}_p = p^{2k-2}$ for the eigenvalues $\lambda_p, \mu_p$ of $\varphi_p$ (citing
  Jacquet [10], p. 33, Li [12] and Ogg [15], as cited there).

## Sources

- P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7 (1974), 507–530,
  [doi:10.24033/asens.1277](https://doi.org/10.24033/asens.1277): Proposition 5.1 and (5.1.1), p. 518 ("Soit f une forme
  modulaire parabolique de type (k, ε) sur Γ₀(N), non identiquement nulle. On suppose que f est fonction propre des
  $T_p$, $p \nmid N$, avec pour valeurs propres $a_p$"), and Démonstration 5.2, pp. 518–519; §1.5, p. 509, for forms of
  type $(k, \varepsilon)$; (1.6.1), p. 509, for $T_p$; §1.7 and (1.7.2), p. 509; §1.8, pp. 509–510; §1.9, p. 510.
- J.-P. Serre, *Cours d'arithmétique*, Presses Universitaires de France, Paris (1970), p. 112, for Landau's lemma, as
  cited in Deligne–Serre (1974), p. 519; not read.
