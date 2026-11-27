# F-matrix bijection for fully heterochronous ranked tree shapes

**Setting.** A *ranked tree shape* is a rooted binary tree shape with $n$ unlabeled leaves together with a total order of its nodes compatible with ancestry. In the *isochronous* case all leaves are sampled at time $0$ and only the $n-1$ internal nodes are ranked; in the *fully heterochronous* case all $2n-1$ nodes, leaves included, are totally ordered (as when a phylogram's branch lengths are discretized). With event times $u_0 > u_1 > \cdots > u_{2n-2}$, time running from leaves to root, the *F-matrix* of the tree has entries $F_{i,j}$ = the number of lineages present during the whole interval $(u_{i+1}, u_j)$, $0 \le j \le i \le 2n-3$.

**Theorem (isochronous case).** Isochronous ranked tree shapes with $n$ leaves are in bijection with lower-triangular $(n-1)\times(n-1)$ nonnegative integer matrices satisfying constraints 1, 2 and 5 below with $2n-3$ replaced by $n-2$, the diagonal $F_{i,i} = i+2$ and the subdiagonal $F_{i,i-1} = i$ ($1 \le i \le n-2$).

**Theorem (fully heterochronous case).** Fully heterochronous ranked tree shapes with $n$ leaves are in bijection with the lower-triangular $(2n-2)\times(2n-2)$ matrices $F$ of nonnegative integers such that
1. rows increase: $F_{i,j-1} \le F_{i,j}$ for $1 \le j \le i \le 2n-3$;
2. columns decrease by at most one: $F_{i-1,j} - 1 \le F_{i,j} \le F_{i-1,j}$ for $0 \le j < i \le 2n-3$;
3. the diagonal is positive with $F_{0,0} = 2$, $F_{i,i} = F_{i-1,i-1} \pm 1$ for $0 < i < 2n-3$ ($-1$ at a sampling event, $+1$ at a coalescent event), and $F_{2n-3,2n-3} = 1$;
4. the subdiagonal is $F_{i,i-1} = F_{i-1,i-1} - 1$ for $1 \le i \le 2n-3$;
5. every remaining entry ($2 \le i \le 2n-3$, $1 \le j \le i-2$) is pinned by its three neighbors:

$$F_{i,j-1} + F_{i-1,j} - F_{i-1,j-1} - 1 \;\le\; F_{i,j} \;\le\; F_{i,j-1} + F_{i-1,j} - F_{i-1,j-1}.$$

**Corollary (diagonals).** Any sequence $f_0 = 2$, $f_i = f_{i-1} \pm 1$, $f_i \le 2n - i - 2$ ($0 \le i \le N \le 2n-3$) of positive integers is the initial diagonal of some such F-matrix.

**Proposition (single-pass filling).** Call a partial filling of the first $N$ rows and the first $M+1$ entries of row $N$ (lexicographic order) an *F-sequence* if its diagonal satisfies the corollary's conditions, its entries off the diagonal and subdiagonal satisfy $L(i,j) \le f_{i,j} \le U(i,j)$ with $L(i,j) = \max(f_{i,j-1},\, f_{i-1,j}-1,\, f_{i,j-1}+f_{i-1,j}-f_{i-1,j-1}-1)$ and $U(i,j) = \min(f_{i-1,j},\, f_{i,j-1}+f_{i-1,j}-f_{i-1,j-1})$ (entries with a negative index read as $0$), and

$$f_{i-1,j} = f_{i-1,i-1} \implies f_{i,j} = f_{i-1,i-1} - 1 .$$

Every F-sequence extends by one entry to an F-sequence (set $f_{N,M+1} = f_{N-1,N-1}-1$ if $f_{N-1,M+1} = f_{N-1,N-1}$, otherwise either bound; the subdiagonal entry is $f_{N-1,N-1}-1$; the next diagonal entry moves by $\pm1$ within the corollary's bounds), so F-matrices can be filled in one pass without backtracking. The last condition is needed: without it a partial matrix can satisfy constraints 1–5 so far and still have no valid completion (the source's $n = 3$ example with rows $2 \mid 1\ 3 \mid 0\ 2\ 2 \mid 0\ 2$ is forced to $F_{3,2} = F_{3,3} = 1$, so $F_{3,1} = 2$ breaks row monotonicity).

## Expansion

The diagonal records the lineage-through-time count, which rises at each coalescence and falls at each sampling, starting from the two lineages below the root and ending with the last sampled leaf. Off-diagonal entries count lineages persisting across longer intervals: moving the interval endpoint by one event either keeps every lineage or removes the single one touched by that event, which gives the row, column and two-sided "parallelogram" constraints. Conversely, the differences $F_{i,j} - F_{i,j-1}$ and $F_{i-1,j} - F_{i,j}$ identify which earlier node each event attaches to, so the tree can be rebuilt one event at a time, proving the bijection. In the isochronous case either bound can be chosen for each entry in lexicographic order; in the heterochronous case the forced-value condition of the proposition must also be respected. With that rule, valid trees can be enumerated or sampled by sequential choices, which defines flexible probability models on tree shapes and distances between them.

## Sources

- C. Jennings-Shaffer, Z. Chen, J. A. Palacios and F. A. Matsen IV, "Generalizing matrix representations to fully heterochronous ranked tree shapes", *Bulletin of Mathematical Biology* 88(5) (2026), 85, Theorems 1, 2, Corollary 1 and Proposition 1, <https://doi.org/10.1007/s11538-026-01632-4> (preprint arXiv:2510.27030).
