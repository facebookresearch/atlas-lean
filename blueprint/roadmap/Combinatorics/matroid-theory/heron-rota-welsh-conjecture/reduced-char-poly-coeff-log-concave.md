# Log-concavity of the reduced characteristic polynomial

For every finite matroid $M$ of rank $r + 1$ and every integer $0 < k < r$,

$$\mu_{k-1}(M) \, \mu_{k+1}(M) \le \mu_k(M)^2 .$$

This is Proposition 9.8 and Theorem 9.9 (1) of Adiprasito, Huh and Katz, stated there for
loopless matroids (with a loop every $\mu_k$ vanishes). Their proof is by induction on the rank:
for $k < r - 1$ it passes to the truncation of $M$, and for $k = r - 1$ it writes the
coefficients as mixed degrees $\mu_k(M) = \deg(\alpha_M^{r-k}\beta_M^k)$ in the Chow ring and
applies the inequality
$\deg(\ell_1^2 \ell_2^{r-2}) \deg(\ell_2^{r}) \le \deg(\ell_1 \ell_2^{r-1})^2$
for a nef class $\ell_2$ (Lemma 9.6, a consequence of the Hodge–Riemann relations in degree
one) to $\ell_1 = \alpha_M$ and $\ell_2 = \beta_M$. Since
$w_k(M) = \mu_k(M) + \mu_{k-1}(M)$, the absolute coefficients of $\chi_M$ are the convolution
of $(\mu_k)$ with $(1, 1)$, and a convolution of log-concave sequences is log-concave; this
gives the [Heron–Rota–Welsh conjecture](characteristic-polynomial-log-concave-ho.md).

## Informally uses

- [Reduced characteristic polynomial coefficients as mixed degrees](../hodge-theory-for-matroids/reduced-char-poly-coeff-eq-deg.md):
  Proposition 9.5 turns the inequality into one between degrees in the Chow ring.

## Background

- [Hodge–Riemann relations for matroids](../hodge-theory-for-matroids/hodge-riemann.md): Lemma 9.6,
  used for $k = r - 1$, is deduced from the Hodge–Riemann relations in degree one
  (Theorem 8.8).

## Sources

- K. Adiprasito, J. Huh and E. Katz, *Hodge theory for combinatorial geometries*, Ann. of
  Math. 188 (2018), 381–452, Lemmas 9.6 and 9.7, Propositions 9.5 and 9.8, Theorem 9.9,
  https://arxiv.org/abs/1511.02888.
