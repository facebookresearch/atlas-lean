# BBBV lower bound in the standard query model

Take the state space $\ell^2(\iota \times W)$, with a query register $\iota$ of $N$ items and a finite
workspace $W$. Let an algorithm apply linear isometries $U_0, \dots, U_T$ with $T$ calls in between to
the [phase oracle marking](marking-oracle.md) $y$, which negates the amplitudes of the basis states
$|y, w\rangle$, starting from a unit vector $\psi_0$. If for every $y$ measuring the query register of the
final state gives $y$ with probability at least $1/2$, that is
$\sum_w |\psi_T^y(y, w)|^2 \ge 1/2$, then

$$N \le 16T^2 + 4 .$$

Search therefore needs $\Omega(\sqrt N)$ queries, the order attained by Grover's algorithm (Bennett,
Bernstein, Brassard and Vazirani, Section 3.1, the query lower bound behind Theorem 3.5; see
[Lower bound for quantum search (BBBV)](mul-card-le-of-forall-success.md) for how the two statements
compare). Other final measurements, given by any linear maps $Q_y$ with $\sum_y \|Q_y v\|^2 \le \|v\|^2$,
are covered by that abstract statement.

## Informally uses

- [Lower bound for quantum search (BBBV)](mul-card-le-of-forall-success.md): applied with $P_y = Q_y$ the [query projection](query-proj.md).
- [Born rule for the query register](norm-query-proj-sq.md): identifies $\|P_y v\|^2$ with the probability of outcome $y$.

## Background

- [Exact success probability of Grover search](../grover-s-algorithm/marked-probability-grover-iterate-unifor.md): the matching upper bound, $\sin^2((2k+1)\theta)$ after $k$ iterations.

## Sources

- C. H. Bennett, E. Bernstein, G. Brassard and U. Vazirani, "Strengths and weaknesses of quantum computing", SIAM Journal on Computing 26 (1997), 1510–1523; arXiv:quant-ph/9701001, Section 3.1 (Definition 3.2, Theorem 3.3, Corollary 3.4, Theorem 3.5).
- E. Bernstein and U. Vazirani, "Quantum complexity theory", SIAM Journal on Computing 26 (1997), 1411–1473; author-hosted version dated September 8, 1997, Theorem 3.4.1 (theorem number as in that version).
