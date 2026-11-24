# Isolated read: alone at its start, no other start within $W$

Let $N$ reads have start positions $s_1, \dots, s_N$ on a circular genome with positions
$\{0, \dots, G-1\}$, and let $W$ be a natural number. A position $p$ holds an isolated read if
exactly one read starts at $p$ and every read starting elsewhere starts more than $W$ positions
after $p$ and more than $W$ positions before it: for every $j$ with $s_j \ne p$,
$(s_j - p) \bmod G > W$ and $(p - s_j) \bmod G > W$. For $W \ge G - 1$ no read can start
elsewhere, so this holds exactly when $N = 1$ and the read starts at $p$.

With $W = L - T$ for reads of length $L$ declared overlapping when they share at least $T$ bases,
and the single-piece condition $2L \le G + 1$ (see [run end](ends-run.md)), such a read forms an
apparent island of exactly one clone.
