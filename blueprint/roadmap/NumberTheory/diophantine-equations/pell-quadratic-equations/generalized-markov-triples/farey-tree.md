# The Farey tree

Write a fraction $n/d$, with $n$ and $d$ natural numbers, for the pair
$(n, d)$, so that $1/0$ stands for $\infty$. The Farey tree $\mathrm{FT}$ is the infinite binary
tree of triples of fractions with root $(0/1, 1/1, 1/0)$ in which a vertex $(a/b, c/d, e/f)$
has left child $(a/b, (a+c)/(b+d), c/d)$ and right child $(c/d, (c+e)/(d+f), e/f)$. For a path
$w$, a finite sequence of left and right moves, this gives the vertex of $\mathrm{FT}$ reached
from the root by making the moves of $w$ in order.

## Sources

- Y. Gyoda and S. Maruyama, *Uniqueness Theorem of Generalized Markov Numbers That Are Prime Powers*, INTEGERS 26 (2026), Article A91, Section 3.2.
