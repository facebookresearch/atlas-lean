# Uniform competitive-ability distributions are the equilibrium strategies

**Game.** There are $n \ge 2$ competing species. In the discrete model the possible competitive abilities are $x_j = j/M$, $j = 0,\dots,M$, and a strategy is a map $B : \{x_j\} \to [0,\infty)$ with abundance $|B| = \sum_j B(x_j) > 0$ and mean competitive ability

$$\mathrm{MCA}(B) = \frac{1}{|B|}\sum_{j=0}^M x_j B(x_j) \le \frac12;$$

$B(x_j)/|B|$ is the probability that a random individual of the species has ability $x_j$. In an encounter the more able individual wins (it replicates and the loser dies) and equal abilities draw. The payoff to species $A_k$ against $A_1,\dots,A_n$ is

$$\wp(A_k; A_{-k}) = \frac{1}{\sum_\ell |A_\ell|}\sum_{j=0}^M A_k(x_j)\Big[\sum_{i<j}\sum_{\ell} A_\ell(x_i) - \sum_{i>j}\sum_\ell A_\ell(x_i)\Big].$$

In the continuous model a strategy is a continuous $f : [0,1] \to [0,\infty)$ with $F(1) = \int_0^1 f > 0$ and $\mathrm{MCA}(f) = \frac{1}{F(1)}\int_0^1 x f(x)\,dx \le \frac12$, with payoff

$$\wp(f_k; f_{-k}) = \frac{1}{\sum_\ell F_\ell(1)}\int_0^1 f_k(x)\Big[\int_0^x \sum_\ell f_\ell(t)\,dt - \int_x^1 \sum_\ell f_\ell(t)\,dt\Big]dx.$$

An equilibrium point is a profile from which no species can raise its payoff by changing only its own strategy.

**Theorem.**
1. Discrete model, $M$ odd: the equilibrium strategies are exactly the strategies with the same positive value at every $x_j$ (uniform over all abilities).
2. Discrete model, $M$ even: $B$ is an equilibrium strategy iff $\mathrm{MCA}(B) = \tfrac12$, $B(x_{2j}) = B(x_0)$ and $B(x_{2j+1}) = B(x_1)$ for all $j$.
3. Continuous model: a strategy is an equilibrium strategy iff it is a positive constant function.
4. In every case, sums of equilibrium strategies are equilibrium strategies, any collection of equilibrium strategies is an equilibrium point, and every equilibrium point consists of equilibrium strategies.

## Expansion

Because encounters are zero-sum, competition within a species does not change its abundance, and the payoff reduces to how a species' ability distribution fares against the pooled distribution of all others. A uniform distribution makes every competitor's expected gain from any ability level balance exactly, so no deviation with mean at most $\tfrac12$ improves its payoff; conversely, for any non-uniform strategy one can construct a competitor with the same mean that beats it, for instance against an invariant (point-mass) strategy a "Lake Wobegon" distribution placing one individual at ability $0$ and the rest slightly above the mean. Biologically, the equilibria have maximal phenotypic heterogeneity, coexist with every strategy of equal mean, resist invasion, and persist even from much lower abundance, whereas invariant species can be driven extinct.

## Sources

- S. Menden-Deuer, J. Rowlett, M. Nursultanov, S. Collins, T. Rynearson, "Biodiversity of marine microbes is safeguarded by phenotypic heterogeneity in ecological traits", PLoS ONE 16(8):e0254799 (2021), Definitions 1–3, Eqs (1)–(4) and Theorem 1 (proofs in S1–S2 Appendices), <https://doi.org/10.1371/journal.pone.0254799>, PMCID PMC8336841.
