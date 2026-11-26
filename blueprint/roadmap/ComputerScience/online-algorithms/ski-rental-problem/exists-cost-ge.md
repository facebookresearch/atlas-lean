# Lower bound for deterministic ski rental, weak form

For every purchase price $B \ge 1$ and every deterministic strategy $s$, there is a season length
$d$ with $(2B - 1) \cdot \mathrm{opt}_B(d) \le B \cdot \mathrm{cost}_B(s, d)$.

As stated, the inequality also holds for the empty season $d = 0$, where both costs are $0$, so it
is not by itself an informative lower bound. The informative form takes $d \ge 1$: for every such
$s$, some season of positive length satisfies the inequality, so on that season $s$ pays at least
$2 - 1/B$ times the offline optimum, which is positive.
