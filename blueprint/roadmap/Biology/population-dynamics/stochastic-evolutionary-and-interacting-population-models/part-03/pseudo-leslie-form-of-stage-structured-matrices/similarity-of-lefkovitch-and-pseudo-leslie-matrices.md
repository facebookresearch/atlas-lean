# Similarity of Lefkovitch and pseudo-Leslie matrices

A stage-structured (Usher or Lefkovitch) population model $\mathbf x_{t+1} = \mathcal L\mathbf x_t$ uses an $n\times n$ matrix with fertilities $f_1,\dots,f_n$ in the first row, transition rates $b_1,\dots,b_{n-1} > 0$ on the subdiagonal and stasis rates $c_1,\dots,c_{n-1}$ on the diagonal below the first row:

$$\mathcal L = \begin{pmatrix} f_1 & f_2 & f_3 & \cdots & f_{n-1} & f_n\\ b_1 & c_1 & 0 & \cdots & 0 & 0\\ 0 & b_2 & c_2 & \cdots & 0 & 0\\ \vdots & & \ddots & \ddots & & \vdots\\ 0 & 0 & 0 & \cdots & b_{n-1} & c_{n-1}\end{pmatrix}, \qquad f_n > 0.$$

A **pseudo-Leslie** matrix has the Leslie shape (first row $\phi_1,\dots,\phi_n$, subdiagonal $b_1,\dots,b_{n-1}$, zeros elsewhere) but its first-row entries may be negative.

For $1 \le i \le n$ and $p \ge 0$ define the signed elementary symmetric sums of the stasis rates

$$\Gamma_i^p = \begin{cases} (-1)^p\displaystyle\sum_{n-1 \ge i_p > \cdots > i_1 \ge i} c_{i_1}\cdots c_{i_p}, & 0 < p \le n-i,\\ 1, & p = 0,\\ 0, & p > n-i,\end{cases} \qquad \Lambda_i^j = \prod_{k=i}^{j} b_k\ \ (i \le j),\quad \Lambda_i^{i-1} = 1.$$

Let $S$ be the upper unitriangular matrix with $s_{i,j} = \Gamma_i^{j-i}/\Lambda_i^{j-1}$ for $j \ge i$, and let $L$ be the pseudo-Leslie matrix with subdiagonal $b_1,\dots,b_{n-1}$ and first row

$$\phi_j = -\frac{\Gamma_1^{j}}{\Lambda_1^{j-1}} + \sum_{k=1}^{j}\frac{\Gamma_k^{j-k}}{\Lambda_k^{j-1}}\,f_k, \qquad j = 1,\dots,n.$$

**Theorem.** For every Lefkovitch matrix, $S^{-1}\mathcal L S = L$. Consequently $\mathcal L^t = S L^t S^{-1}$, and $\mathcal L$ and $L$ share the characteristic polynomial and the dominant eigenvalue $\lambda$.

**Markov matrices.** For a population matrix $A$ with dominant eigenvalue $\lambda$ and positive right Perron eigenvector $\mathbf u$, let $P^A$ have entries $p^A_{ij} = a_{ij}u_j/(\lambda u_i)$. If $\mathcal L$ (irreducible) and the pseudo-Leslie $L$ are similar, then $P^{\mathcal L}$ and $P^{L}$ are similar stochastic matrices; however their stationary distributions differ, and so do the population (Kolmogorov–Sinai) entropies $H_A = -\sum_{i,j}\pi_i p^A_{ij}\log p^A_{ij}$, even though the growth rate $\lambda$ is the same.

*Example.* $\mathcal L = \begin{pmatrix}1 & 3\\ 0.4 & 0.55\end{pmatrix}$ gives $S = \begin{pmatrix}1 & -1.375\\ 0 & 1\end{pmatrix}$ and $L = \begin{pmatrix}1.55 & 1.625\\ 0.4 & 0\end{pmatrix}$, both with $\lambda \approx 1.89331$.

## Depends on

- [Leslie matrix](../../../leslie-matrix-model/leslie-matrix.md)

## Expansion

Conjugation by an upper unitriangular $S$ keeps the subdiagonal $b_k$ and can be chosen column by column to clear the diagonal stasis terms $c_k$, pushing their effect into the first row. The recursion $\Gamma_i^{p+1} = c_{i-1}\Gamma_i^p + \Gamma_{i-1}^{p+1}$ (Lemma 2) is the bookkeeping identity that makes $\mathcal L S = S L$ hold entrywise. The payoff is computational: powers and the characteristic polynomial $\lambda^n - \phi_1\lambda^{n-1} - \cdots - \phi_n$ of a Leslie-shaped matrix are explicit. The Markov chains $P^A$ describe ancestry of individuals backward along the stable stage distribution; similarity preserves their spectrum but not their entropy, so entropy-based life-history comparisons depend on the stage parametrization.

## Sources

- João F. Alves, Henrique M. Oliveira, "Similarity of general population matrices and pseudo-Leslie matrices", arXiv (2015). Section 2 (Theorem 1, Lemma 2), Section 3 (Example 3, Propositions 4–6, Remark 7). <https://doi.org/10.48550/arXiv.1503.06308>. Published version: Applied Mathematics & Information Sciences 9(5) (2015), 2239–2244, <https://doi.org/10.12785/amis/090504>; locators above refer to the arXiv version.
