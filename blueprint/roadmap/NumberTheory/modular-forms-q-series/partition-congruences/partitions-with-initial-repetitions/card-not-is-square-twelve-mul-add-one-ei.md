# Residues $r$ with $12r + 1$ and $8r + 1$ both non-squares modulo $p$

For every prime $p$,
let $N$ be the number of integers $r$ with $1 \le r \le p - 1$ such that neither $12r + 1$ nor
$8r + 1$ is a square modulo $p$. Then $N = \lfloor p/4 \rfloor - 1$ if $p \equiv 5 \pmod{24}$,
$N = \lfloor p/4 \rfloor + 1$ if $p \equiv 11 \pmod{24}$, and $N = \lfloor p/4 \rfloor$ otherwise.

Here $0$ counts as a square modulo $p$, so "not a square" means "quadratic nonresidue". The paper
assumes $p \ge 5$; for $p = 2$ and $p = 3$ both sides are $0$. If $0$ were counted as a non-square,
the count at $p = 5$ would be $2$ instead of $0$.

## Sources

- John Greene and James A. Sellers, *Extending Recent Parity Results of Nyirenda and Mugwangwavari for Partitions with Initial Repetitions*, INTEGERS 25 (2025), Article A32, Theorem 8.
