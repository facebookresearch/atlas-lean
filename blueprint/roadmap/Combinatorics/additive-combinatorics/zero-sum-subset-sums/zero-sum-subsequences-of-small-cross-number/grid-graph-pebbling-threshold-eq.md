# Bushaw–Kettle pebbling threshold for grids

Let $d \ge 1$ and let $w_0, \dots, w_{d-1}$
be natural numbers with $w_i \ge 2$ for every $i$. For each $k$ give the grid $P_k^d$ on
$\{0, \dots, k-1\}^d$ the cost $w_i$ on every edge in coordinate $i$, and let
$t : \mathbb{N} \to \mathbb{R}$ be a threshold function, as $k \to \infty$, for the probability
that a uniformly random configuration of $s$ pebbles on $P_k^d$ is solvable. Write $\lg = \log_2$
and

$$
A(k) = \left(\frac{(d+1)! \prod_{i\lt d} \lg w_i}{2} \lg k\right)^{1/(d+1)} -
\frac{d}{d+1} \lg \lg k.
$$

Then there is a real constant $C$ such that for all sufficiently large $k$,

$$
k^d e^{A(k) - C} \le t(k) \le k^d e^{A(k) + C},
$$

that is, with $n = k^d$, $t(k) = n \exp[A(k) + O(1)]$.

The hypothesis $w_i \ge 2$ is not part of the quoted statement: with all costs equal to $1$
every nonempty configuration is solvable, so the thresholds are bounded while the right side
tends to infinity. Likewise $d \ge 1$ excludes $d = 0$, where the grid is a single vertex.

## Sources

- Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in Abelian Groups*, INTEGERS 24 (2024), Article A93, Theorem 9 (quoting Bushaw and Kettle).
