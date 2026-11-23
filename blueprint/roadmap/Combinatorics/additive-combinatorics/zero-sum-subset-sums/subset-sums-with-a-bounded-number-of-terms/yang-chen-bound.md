# The Yang–Chen bound

Let $k, h \in \mathbb{N}$ and $\bar r = (r_0, \dots, r_{k-1})$ with
all $r_j \in \mathbb{N}$; all sums below run over indices $j \in \{0, \dots, k-1\}$. Let $\mu$ be
the largest $m \in \{0, \dots, k\}$ with $\sum_{j < m} r_j \le h$, let $\eta$ be the integer such
that $\eta + 1$ is the least $m \in \{0, \dots, k\}$ with $\sum_{j \ge m} r_j \le h$ (so
$\eta = -1$ when $h \ge \sum_j r_j$), and set $\delta = h - \sum_{j < \mu} r_j$ and
$\theta = h - \sum_{j > \eta} r_j$. The Yang–Chen bound is the integer

$$L(\bar r, h) = \sum_{j > \eta} j r_j - \sum_{j < \mu} j r_j + \theta \eta - \delta \mu + 1.$$

## Sources

- Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24 (2024), Article A116, Section 1.1 (definitions of `μ`, `η`, `δ`, `θ` and `L(r̄, h)`).
