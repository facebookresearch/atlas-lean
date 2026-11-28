# Local score p-values by Markov chain imbedding

**General imbedding.** Let $(X_j)$ be a Markov chain on $L-1$ transient states and one absorbing state, with transition matrix in block form

$$\Pi=\begin{pmatrix}R&v\\0&1\end{pmatrix},\qquad\text{so that}\qquad \Pi^n=\begin{pmatrix}R^n&\sum_{j=0}^{n-1}R^jv\\0&1\end{pmatrix}\quad(n\ge 1).$$

Hence, given $X_1=s$ transient, the probability of absorption by time $n$ is the $s$-th entry of $\sum_{j=0}^{n-2}R^jv$, accumulated with the vector recurrence $x_0=v$, $x_{j+1}=Rx_j$; the complementary probability is the $s$-th entry of $R^{n-1}\mathbf 1$, computed by the same recurrence started from $x_0=\mathbf 1$. Computing whichever of the two probabilities is small directly avoids cancellation error.

**Local score.** For real scores $S_1,\dots,S_n$, the local score

$$H_n=\max_{1\le i\le j\le n}\sum_{k=i}^{j}S_k$$

is the largest segment sum. With $U_0=0$ and $U_j=\max\{0,U_{j-1}+S_j\}$ (Lindley's recursion), $H_n=\max_jU_j$, computable in $O(n)$. For i.i.d. integer scores and a threshold $a>0$, the event $\{H_n\ge a\}$ is absorption of the chain $\min(U_j,a)$ on $\{0,1,\dots,a-1\}\cup\{a\}$, whose transient block $R$ has at most $a^2$ nonzero entries, so $\mathbb P(H_n\ge a)$ is computed exactly in $O(na^2)$ time.

**Asymptotics.** If $R$ is diagonalizable with largest eigenvalue $0<\lambda<1$ and second largest eigenvalue magnitude $\nu$, then $R^i-\lambda^iR_\infty=O(\nu^i)$ uniformly in $i$ with $R_\infty=\lim_iR^i/\lambda^i$, so $\mathbb P(H_n<a)$ decays geometrically like $\lambda^n$, with an explicit error term of order $\nu^\alpha$ when the first $\alpha$ steps are computed exactly.

## Proof depends on

- [Perron–Frobenius theorem for primitive nonnegative matrices](../../../../LinearAlgebra/special-matrices/perron-frobenius-theorem/perron-frobenius-for-primitive-nonnegative-matri.md)

## Expansion

The block identity follows by induction on $n$: each multiplication by $\Pi$ multiplies the transient block by $R$ and adds the absorbed mass $R^{n-1}v$. The local-score chain records the current excursion of the Lindley process above $0$ and stops it at $a$; sequences with rational scores reduce to integers by scaling, and Markov sequences are handled by taking the product of the score state with the previous letter. The spectral bound is the Perron–Frobenius expansion of an irreducible substochastic matrix: $\lambda\le 1$ is real, and primitivity gives $\lambda>\nu$ and a positive $R_\infty$. The same machinery yields exact pattern-count statistics through a chain on (automaton state, count).

## Sources

- G. Nuel, "Effective p-value computations using Finite Markov Chain Imbedding (FMCI): application to local score and to pattern statistics", Algorithms for Molecular Biology 1 (2006) 5, <https://doi.org/10.1186/1748-7188-1-5>, PMCID PMC1479348. Section 2 (Proposition 1, Corollaries 2–3), Section 3 (Eq. (10), Proposition 4, Corollary 5) and Appendix A (Proposition 14, Corollary 15).
