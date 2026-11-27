# Run end: a read start with no start at offsets $1, \dots, V$ after it

Let $N$ reads have start positions $s_1, \dots, s_N$ on a circular genome with positions
$\{0, \dots, G-1\}$, and let $V$ be a natural number. A position $p$ is a run end (for the window
$V$) if some read starts at $p$ and no read starts at a positive offset $1, \dots, V$ after $p$:
there is no $j$ with $0 < (s_j - p) \bmod G \le V$. Reads starting at $p$ itself are allowed, so
run ends are positions, not reads. For $V \ge G - 1$ the condition says that there is at least
one read and every read starts at $p$.

In Lander and Waterman's model, reads of length $L$ are declared overlapping when they share at
least $T$ bases ($1 \le T \le L$); take $V = W := L - T$. When $2L \le G + 1$, two reads starting
at $p$ and $p + d$ with $0 < d < L$ share the single interval of $L - d$ bases, so their overlap
is detected exactly when $d \le W$, and a run end is the last start of an apparent island. This
is an end statistic, not an island count: when at least one run end exists every apparent island
has exactly one, but if $N > 0$ and every gap between consecutive starts is at most $W$, the
circle is one island with no run end.
