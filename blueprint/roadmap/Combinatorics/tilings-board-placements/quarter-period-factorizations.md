# Quarter-period factorizations of the triangular tiling numbers

Let
$Q \colon \mathbb{N} \to \mathbb{N}$ satisfy $Q(0) = Q(1) = 1$, $Q(2) = 4$ and
$Q(n) = Q(n-1) + 3Q(n-2) + Q(n-3)$ for every $n \ge 3$. Then for every $m \ge 1$,

$$Q(4m) = (2Q(2m-1) + 1)(2Q(2m) - 1),$$



$$Q(4m+1) = (2Q(2m) - 1)^2,$$



$$Q(4m+2) = 2(Q(2m-1) + Q(2m))(Q(2m) + Q(2m+1)),$$



$$Q(4m+3) = 2(Q(2m) + Q(2m+1))^2.$$

All values of $Q$ are at least $1$, so the subtractions above are exact. In the source, $Q(n)$ is
the number of tilings of a triangular strip.

## Sources

- Mark Shattuck, "Combinatorial Proofs of Some Formulas for Triangular Tilings," Journal of Integer Sequences 17 (2014), Article 14.5.5, Theorem (label thm2, due to Bodeen et al.), lines 103–112, https://cs.uwaterloo.ca/journals/JIS/VOL17/Shattuck/shattuck8.tex
- the recurrence and initial values are equation (rec) at lines 122–125.
