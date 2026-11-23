# Reduced characteristic polynomial coefficients as mixed degrees

For a finite loopless matroid $M$ of rank $r + 1$, its degree map $\deg$, any element
$i$ of the ground set and every $k \le r$,

$$\mu_k(M) = \deg\bigl(\alpha_M^{\,r-k} \, \beta_M^{\,k}\bigr),$$

where $\mu_k(M)$ is the unsigned coefficient of $\lambda^{r-k}$ in
$\chi_M(\lambda)/(\lambda - 1)$.

This is Proposition 9.5 of Adiprasito, Huh and Katz, proved by expressing
$\alpha_M^{r-k}\beta_M^k$ through initial descending flags of flats (Lemmas 9.3 and 9.4)
and Proposition 5.8. For a matroid realised by a hyperplane arrangement in an
$r$-dimensional subspace $V \subseteq \mathbb{P}^n$, Huh and Katz had shown that the closure
$\widetilde{V}$ of the graph of the Cremona transformation on $V$ minus the arrangement has
class $[\widetilde{V}] = \sum_{k=0}^{r} \mu_k(M) \, [\mathbb{P}^{r-k} \times \mathbb{P}^{k}]$
in $\mathbb{P}^n \times \mathbb{P}^n$ (their Theorem 1.1).

## Background

- [Coefficients $\mu_k$ of the reduced characteristic polynomial](../heron-rota-welsh-conjecture/reduced-char-poly-coeff.md):
  the numbers $\mu_k(M)$.

## Sources

- K. Adiprasito, J. Huh and E. Katz, *Hodge theory for combinatorial geometries*, Ann. of
  Math. 188 (2018), 381–452, Lemmas 9.3 and 9.4, Proposition 9.5, https://arxiv.org/abs/1511.02888.
- J. Huh and E. Katz, *Log-concavity of characteristic polynomials and the Bergman fan of
  matroids*, Math. Ann. 354 (2012), 1103–1116, Theorem 1.1, https://arxiv.org/abs/1104.2519.
