# Communication lower bound for classical matrix multiplication

Let $n$, $m$, $r$, $s$, $M$ and $W$ be natural numbers and let $\Sigma_1, \dots, \Sigma_s$ be sets of triples $(i, j, k)$ with $i < n$, $j < m$, $k < r$ such that every such triple lies in some $\Sigma_t$, each $\Sigma_t$ has at most $4M$ distinct pairs $(i, k)$, at most $4M$ distinct pairs $(j, k)$ and at most $4M$ distinct pairs $(i, j)$, and $M(s - 1) \le W$ (truncated subtraction). Then

$$\frac{n m r}{8 \sqrt{M}} - M \le W,$$

the quotient being $0$ when $M = 0$.

In words: multiplying a dense $n \times r$ matrix $A$ by a dense $r \times m$ matrix $B$ by evaluating all $n m r$ products $A(i, k) B(k, j)$, on a machine with a fast memory of $M$ words whose execution is cut into $s$ segments satisfying the hypotheses of the [bandwidth lower bound](card-div-sub-le-words.md), moves at least $nmr/(8\sqrt M) - M$ words between fast and slow memory (Corollary 4 of G. Ballard, J. Demmel, O. Holtz and O. Schwartz, *Minimizing communication in linear algebra*, arXiv:0905.2485). For square matrices this is the $\Omega(n^3/\sqrt{M})$ bound of J.-W. Hong and H. T. Kung, *I/O complexity: the red-blue pebble game*, STOC 1981, as restated in Lemma 2.1 of D. Irony, S. Toledo and A. Tiskin, *Communication lower bounds for distributed-memory matrix multiplication*, J. Parallel Distrib. Comput. 64 (2004), 1017–1026. Their Theorem 7.1 proves it with explicit constants through the discrete Loomis–Whitney inequality: at least $n^3/(2\sqrt{2}\,\sqrt{M}) - M$ words for $n \times n$ matrices, with an accounting of at most $2M$ operands of each kind per phase; the constant $8$ here comes from the $4M$ accounting of Ballard, Demmel, Holtz and Schwartz, which also allows the arrays to alias. Blocked algorithms that multiply $\sqrt{M/3} \times \sqrt{M/3}$ blocks attain the bound up to a constant factor.

For $M \ge 1$ the bound is nonpositive, hence vacuous, when $nmr \le 8M^{3/2}$. For example, a $4 \times 4$ product cut into eight $2 \times 2 \times 2$ blocks satisfies the hypotheses with $M = 4$, where the bound is $0$, and a $3 \times 3$ product with $M = 1$ gives the positive bound $27/8 - 1$.

## Informally uses

- [Bandwidth lower bound, segment-counting form](card-div-sub-le-words.md): applied with $G$ the full set of $n m r$ index triples.
