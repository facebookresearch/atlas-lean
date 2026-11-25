# Selberg's $\Lambda^2$ upper bound sieve, finite form

Let $A$ be a finite set of natural numbers, $P \ne 0$ and $\lambda : \mathbb N \to \mathbb R$ with $\lambda_1 = 1$. Then

$$\#\{n \in A : \gcd(P, n) = 1\} \le \sum_{d \mid P} \sum_{e \mid P} \lambda_d \lambda_e \, \#\{n \in A : \operatorname{lcm}(d, e) \mid n\}.$$

The bound holds for every choice of the real numbers $\lambda_d$; Selberg's method then chooses them, subject to $\lambda_1 = 1$ and $\lambda_d = 0$ for large $d$, to minimise the main term. In Heath-Brown's notation this is the first two lines of (1.7) for the weights (2.1), with $\#\mathcal A_d$ for the multiples of $d$ in $A$.

## Informally uses

- [Selberg's $\Lambda^2$ inequality, pointwise](indicator-coprime-le-sq-sum.md): summed over $n \in A$; expanding the square and exchanging sums gives the right side.

## Background

- Selberg's sieve in its weighted form gives the analogous bound for a squarefree $P$ and a weighted sifted set; the statement here does not need $P$ to be squarefree.

## Related topics

- [Selberg's upper bound with the optimal level weights](sifted-sum-le-total-mass-div-level-sum-a.md): the same bound for weighted sets with the optimal $\lambda_d$.

## Sources

- D. R. Heath-Brown, "Lectures on sieves", arXiv:math/0209360 (2002), Sections 1–2.
