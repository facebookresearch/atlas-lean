# Monochromatic sets that are large relative to their gap size

Let $r, t \in \mathbb{N}$ with
$t \ge 1$, and let $f : \mathbb{N} \to \mathbb{N}$ be nondecreasing. There is $B \in \mathbb{N}$
such that for every coloring of $\mathbb{N}^t$ with $r$ colors there is a finite monochromatic set
$S \subseteq [0, B)^t$ with $|S| > f(\operatorname{gs}(S))$, where $\operatorname{gs}(S)$ is the gap
size of $S$ and $[0, B)^t$ is the set of points $x$ with $0 \le x_i < B$ for every coordinate $i$.
This box is the translate of the paper's $[1, B]^t$ by subtracting one in each coordinate.

The paper takes the smallest such $B$, which exists once some $B$ does. Only the restriction of the
coloring to $[0, B)^t$ matters. The hypothesis $t \ge 1$ is the paper's; for $t = 0$ and $r \ge 1$
the statement fails when $f(1) \ge 1$, since the only point gives $|S| = 1 = \operatorname{gs}(S)$.
The statement also holds for $r = 0$, vacuously, since there is then no coloring.

## Sources

- Tom C. Brown, *Piecewise Syndetic Sets in $\mathbb{N}^t$ and $\mathbb{N}^X$*, INTEGERS 24 (2024), Article A2, Theorem 2.
