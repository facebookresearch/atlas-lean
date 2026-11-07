# Stacked graphs of increasing functions in three dimensions

Let $a > 0$, $b$ and $c > 0$
be real numbers and let $f : \mathbb{R} \to \mathbb{R}$ be strictly increasing on $[0, a]$ with
$(f(t) - f(s)) / (t - s) \le b$ whenever $0 \le s < t \le a$. Let
$P = \{(t, f(t)) : t \in [0, a]\}$ be the graph of $f$ over $[0, a]$ and, for $k \ge 1$, let
$Q_{P,k,c} = \{(x, y, ic) : (x, y) \in P,\ i \in \{1, \dots, k\}\} \subseteq \mathbb{R}^3$. Then,
as the real number $n \to \infty$, $\mathrm{opx}(n, Q_{P,2,c}, 3) = \Theta(n^{5/2})$ and
$\mathrm{opx}(n, Q_{P,3,c}, 3) = \Theta(n^{8/3})$.

The hypothesis $a > 0$ excludes the degenerate cases where the graph $P$ is a single point
($a = 0$) or empty ($a < 0$).

## Sources

- Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Corollary 5.18 (`integers-2024-A1-cor-5-18`).
