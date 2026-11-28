# Closed-form minimum total cophenetic index via halving recurrences

**Setting.** Many extremal values of phylogenetic balance indices over rooted binary trees with $n$ leaves are attained by maximally balanced trees and satisfy *divide-and-conquer dividing by a half* recurrences

$$x_n=a\,x_{\lceil n/2\rceil}+a\,x_{\lfloor n/2\rfloor}+p\big(\lceil n/2\rceil,\lfloor n/2\rfloor\big),\qquad n\ge2,$$

with $p$ a polynomial. Write the binary decomposition $n=\sum_{j=1}^{s_n}2^{q_j(n)}$ with $0\le q_1(n)<\dots<q_{s_n}(n)$, so $q_{s_n}(n)=\lfloor\log_2n\rfloor$. The total cophenetic index $\Phi(T)$ of a rooted tree is the sum, over all pairs of leaves, of the depth of their lowest common ancestor; the Sackin index is the sum of leaf depths.

**Theorem (explicit solution).** For every polynomial independent term in $\lceil n/2\rceil$ and $\lfloor n/2\rfloor$ and every initial value $x_1$, the solution $x_n$ is an explicit finite expression in $n$, the exponents $q_j(n)$ and the partial sums $M_i(n)=\sum_{j\ge i}2^{q_j(n)}$, involving Bernoulli numbers (rather than only its $\Theta$ order given by the Master Theorem).

**Corollary (minimum Sackin and total cophenetic indices).** The minimum Sackin index $S_n$ ($S_n=S_{\lceil n/2\rceil}+S_{\lfloor n/2\rfloor}+n$, $S_1=0$) and the minimum total cophenetic index $\Phi_n$ ($\Phi_n=\Phi_{\lceil n/2\rceil}+\Phi_{\lfloor n/2\rfloor}+\binom{\lceil n/2\rceil}2+\binom{\lfloor n/2\rfloor}2$, $\Phi_1=0$) over rooted binary trees with $n$ leaves are

$$S_n=\big(q_{s_n}(n)+2\big)n-2^{q_{s_n}(n)+1},\qquad \Phi_n=\binom n2-s_n\,n-\sum_{i=1}^{s_n}2^{q_i(n)-1}\big(q_i(n)-2i\big).$$

For example, $n=3=2^0+2^1$ gives $\Phi_3=3-6-(-\tfrac12\cdot2-3)=1$, the single cherry of the tree $((a,b),c)$, and $n=2^k$ gives $S_n=k2^k$ and $\Phi_n=\binom{2^k}2-2^k-2^{k-1}(k-2)$.

## Expansion

Both indices are additive over the two subtrees at the root, plus a term counting how much the root split adds: every leaf gains one unit of depth (Sackin), and every pair of leaves on the same side gains one unit of LCA depth (cophenetic). Since both are minimized by trees whose root splits are as even as possible, the minima satisfy the halving recurrences above. Solving them amounts to unrolling the binary expansion of $n$: the tree splits into perfect subtrees of sizes $2^{q_j(n)}$, and the contributions of the levels are summed with the general formula, using Faulhaber-type sums with Bernoulli numbers for polynomial terms. No closed expression for $\Phi_n$ had been published before; the same method handles other indices such as the maximum rooted quartet index.

## Sources

- Tomás M. Coronado, Arnau Mir and Francesc Rosselló, "Explicit solution of divide-and-conquer dividing by a half recurrences with polynomial independent term", PLOS ONE 17 (2022), e0274448, <https://doi.org/10.1371/journal.pone.0274448>; numbering as in arXiv:2111.12313: Section 2 (main theorem) and Section 3 (Examples 2 and 8: minimum Sackin and minimum total cophenetic indices).
