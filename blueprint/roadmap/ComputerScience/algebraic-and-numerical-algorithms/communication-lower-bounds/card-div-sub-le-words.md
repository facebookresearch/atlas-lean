# Bandwidth lower bound, segment-counting form

Let $I$, $J$, $L$ be sets with decidable equality. For a set $\Sigma$ of triples $(i, j, k) \in I \times J \times L$, its three projections are $\{(i, k)\}$, $\{(j, k)\}$ and $\{(i, j)\}$, the sets of pairs obtained by forgetting $j$, $i$ and $k$ respectively. Let $G \subseteq I \times J \times L$ be finite, let $s$, $M$ and $W$ be natural numbers, and let $\Sigma_1, \dots, \Sigma_s$ be finite sets of triples such that

- the $\Sigma_t$ cover $G$: $G \subseteq \Sigma_1 \cup \dots \cup \Sigma_s$;
- each of the three projections of each $\Sigma_t$ has at most $4M$ elements;
- $M(s - 1) \le W$, with truncated subtraction ($s - 1 = 0$ when $s = 0$).

Then, in the real numbers,

$$\frac{|G|}{8\sqrt{M}} - M \le W,$$

where for $M = 0$ the quotient is $0$ (division by zero gives $0$), so that the inequality is trivial.

Interpretation: $G$ is the set of index triples whose $g_{ijk}(a(i,k), b(k,j))$ a computation of the form

$$c(i,j) = f_{ij}\big(g_{ijk}(a(i,k), b(k,j)) \text{ for } k \in S_{ij}, \dots\big)$$

evaluates, on a machine with a fast memory of $M$ words. The execution is cut into $s$ segments, every segment but possibly the last containing $M$ loads and stores, so that the number $W$ of words moved satisfies $M(s - 1) \le W$; $\Sigma_t$ is the set of evaluations of segment $t$, and its projections are the operands $a(i, k)$, $b(k, j)$ and $c(i, j)$ it uses. The segment structure and the operand count are thus hypotheses, and the conclusion is pure counting. Aliasing between the arrays $a$, $b$ and $c$ is allowed, since each projection is bounded separately. The model covers classical matrix multiplication, LU, Cholesky and $LDL^T$ factorisations, dense or sparse; it does not cover Strassen-like algorithms.

This is Theorem 2 of G. Ballard, J. Demmel, O. Holtz and O. Schwartz, *Minimizing communication in linear algebra*, arXiv:0905.2485 (2009); the theorem and corollary numbers on this topic refer to that arXiv version, the journal version (*Minimizing communication in numerical linear algebra*, SIAM J. Matrix Anal. Appl. 32 (2011)) being numbered differently. The source assumes no operand is created and discarded within a segment without memory traffic (no "S2/D2" operands); under that assumption each segment uses at most $4M$ operands of each kind.

For $M \ge 1$ the bound is nonpositive, hence vacuous, when $|G| \le 8 M^{3/2}$, that is when the whole computation fits in about one segment; it is informative only for $|G| \gg M^{3/2}$. For example, for $3 \times 3$ matrix multiplication ($|G| = 27$) with $M = 1$ it gives $27/8 - 1 > 0$. After Theorem 2 the source notes the refinement $\max(|G|/(8\sqrt M) - M,\ \#\text{inputs} + \#\text{outputs})$. Dividing by the largest message size $M$ gives the latency bound $|G|/(8 M^{3/2}) - 1$ messages of Corollary 3 of the same arXiv version.

## Informally uses

- [Evaluations per segment](card-le-of-card-image-le.md): each segment performs at most $8 M\sqrt{M}$ evaluations, so $s \ge |G| / (8 M \sqrt{M})$.
