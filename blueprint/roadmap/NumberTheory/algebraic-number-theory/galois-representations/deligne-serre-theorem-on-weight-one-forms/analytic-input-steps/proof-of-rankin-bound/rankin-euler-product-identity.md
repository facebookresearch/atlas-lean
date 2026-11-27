# Rankin's Euler product for the squared coefficients of a primitive form

Let $N \ge 1$, let $\varepsilon$ be a Dirichlet character mod $N$ and $k \ge 1$ an integer with $\varepsilon(-1) = (-1)^k$, and let
$f = \sum_{n \ge 1} a_n q^n$ be a [primitive form](primitive-forms-of-type-k-epsilon.md) of type $(k, \varepsilon)$ on
$\Gamma_0(N)$. For each prime $p \nmid N$ choose $\varphi_p \in \mathrm{GL}_2(\mathbb{C})$ with $\operatorname{Tr}(\varphi_p) = a_p$ and
$\det(\varphi_p) = \varepsilon(p) p^{k-1}$, and let $\overline{\varphi}_p$ be its complex conjugate. Then for every prime
$p \nmid N$, as formal power series in $X$,

$$\sum_{r \ge 0} |a_{p^r}|^2 X^r = \frac{1 - p^{2k-2} X^2}{\det(1 - \varphi_p \otimes \overline{\varphi}_p\, X)},$$

and for $\operatorname{Re}(s) > k$ the product $L(s) = \prod_{p \nmid N} \det(1 - \varphi_p \otimes \overline{\varphi}_p\, p^{-s})^{-1}$
converges absolutely and

$$L(s) = H(s)\, \zeta(2s - 2k + 2) \sum_{n \ge 1} |a_n|^2 n^{-s}, \qquad H(s) = \prod_{p \mid N} (1 - p^{-2s + 2k - 2})(1 - |a_p|^2 p^{-s}).$$

Here $N$ is the level of the primitive form $f$ itself.
[Rankin's bound](rankin-bound-for-the-mean-square-of-hecke-eigenvalues.md) applies this to the primitive form $f_0$ of a
level $M$ that divides the level of the eigenform it starts from, so that there these formulas hold at level $M$, with
the primes dividing $M$ in the place of those dividing $N$.

Deligne and Serre state the identity for $L(s)$ in Démonstration 5.2, from
$\lambda_p \overline{\lambda}_p \mu_p \overline{\mu}_p = |\varepsilon(p) p^{k-1}|^2 = p^{2k-2}$ for the eigenvalues $\lambda_p, \mu_p$ of
$\varphi_p$, citing Jacquet, Li and Ogg. By the Euler factors of $f$, $a_{p^r} = h_r(\lambda_p, \mu_p)$ with
$h_r(\alpha, \beta) = \sum_{i + j = r} \alpha^i \beta^j$, and the local identity is the case $\alpha = \lambda_p$, $\beta = \mu_p$,
$\gamma = \overline{\lambda}_p$, $\delta = \overline{\mu}_p$ of the identity of formal power series

$$\sum_{r \ge 0} h_r(\alpha, \beta)\, h_r(\gamma, \delta)\, X^r = \frac{1 - \alpha\beta\gamma\delta X^2}{(1 - \alpha\gamma X)(1 - \alpha\delta X)(1 - \beta\gamma X)(1 - \beta\delta X)},$$

whose coefficients are polynomials in $\alpha, \beta, \gamma, \delta$; Ogg proves it in his normalization by cross-multiplying
(Proposition, p. 305). For $p \mid N$, $a_{p^r} = a_p^r$ gives $\sum_r |a_{p^r}|^2 p^{-rs} = (1 - |a_p|^2 p^{-s})^{-1}$. For
$\operatorname{Re}(s) > k$ the series $\sum_n |a_n|^2 n^{-s}$ converges absolutely and has multiplicative coefficients, so it is
the product of its local series $\sum_r |a_{p^r}|^2 p^{-rs}$. For $p \nmid N$ the local series therefore converges for
$|X| < p^{-k}$, where it equals the rational function above; its numerator has no zero there, so neither has
$\det(1 - \varphi_p \otimes \overline{\varphi}_p\, X)$, and the factor of $L(s)$ at $p$ is
$(1 - p^{2k-2-2s})^{-1} \sum_r |a_{p^r}|^2 p^{-rs}$. Multiplying over $p$ with $\zeta(2s - 2k + 2) = \prod_p (1 - p^{2k-2-2s})^{-1}$,
absolutely convergent for $\operatorname{Re}(s) > k - 1/2$, gives the identity for $L(s)$.

## Depends on

- [Primitive forms of type (k, ε) on Γ₀(N)](primitive-forms-of-type-k-epsilon.md)

## Proof depends on

- [Hecke relations and Euler product of a primitive form](euler-product-of-a-primitive-form.md), for the multiplicativity of the $a_n$ and the series $\sum_r a_{p^r} X^r$
- [Rankin–Selberg series of a primitive form](../proof-of-the-rankin-selberg-continuation/rankin-selberg-series-of-a-primitive-form.md), for the convergence of $\sum_n |a_n|^2 n^{-s}$ on $\operatorname{Re}(s) > k$

## Expansion

This node is still to be broken down. A good expansion states and links:

- the identity of formal power series above, by cross-multiplication (Ogg, Proposition, p. 305; Jacquet [10], p. 33, as
  cited in Deligne–Serre, p. 518);
- the Euler product of an absolutely convergent Dirichlet series with multiplicative coefficients, for
  $\sum_n |a_n|^2 n^{-s}$, and the Euler product of $\zeta$.

## Sources

- P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. École Norm. Sup. (4) 7 (1974), 507–530,
  [doi:10.24033/asens.1277](https://doi.org/10.24033/asens.1277): Démonstration 5.2, p. 518 (the definition of $L(s)$, its
  four-factor Euler product and the identity $\mathrm{L}(s) = \mathrm{H}(s)\zeta(2s-2k+2)\bigl(\sum_{n=1}^{\infty} |a_n|^2 n^{-s}\bigr)$);
  (1.7.2), p. 509.
- A. P. Ogg, *On a convolution of L-series*, Invent. Math. 7 (1969), 297–312: Proposition and its proof, p. 305.
- H. Jacquet, *Automorphic Forms on GL(2), Part II*, Lecture Notes in Math. 278, Springer (1972): p. 33, as cited in
  Deligne–Serre (1974), p. 518; not read.
