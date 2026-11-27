# Logarithmic vision radius suffices for near-shortest crossing of a percolation maze

Consider bond percolation on $\mathbb{Z}^2$ with edge-open probability $p > p_c = 1/2$, conditioned on the almost-sure events that the open edges have a unique infinite cluster $C^\infty$ and all closed clusters are finite. Use the sup-norm $\|(x, y)\| = \max(|x|, |y|)$. Let $s = (0, 0)$ and $t = (d, 0)$ lie in $C^\infty$. For $\alpha > 0$ let $S_\alpha = [0, d] \times [-W/2, W/2]$ be the strip of width $W = \alpha \log d$, and let $\tilde D_\alpha$ be the length of a shortest path in $S_\alpha \cap C^\infty$ joining its left border to its right border. A walker has **vision radius** $r$ if at node $u$ it sees every edge of the ball $B_r(u) = \{v : \|v - u\| \le r\}$ and may compute arbitrarily with that view. "With high probability" means with probability at least $1 - 1/d^2$.

**Theorem (Appendix 3, Lemma 1 and Theorem 3 of the source).**

1. There is $\alpha'$ such that for every $\alpha > \alpha'$, with high probability $S_\alpha \cap C^\infty$ contains a path from the left to the right border, so $\tilde D_\alpha < \infty$.
2. For $\alpha$ as in part 1, every $\epsilon > 0$ and all sufficiently large $d$, there is a constant $\gamma > \alpha$ such that, with high probability, a walker with vision radius $\gamma \log d$ finds a path from $s$ to $t$ of length at most $(1 + \epsilon)\, \tilde D_\alpha$.

## Depends on

- [Critical probability of the square lattice](../../../../Probability/percolation/phase-transition/critical-probability-of-the-square-lattice/pc-two-eq-half.md)
- [Percolation critical probability](../../../../Probability/percolation/phase-transition/percolation-probability-and-critical-point/pc.md)
- [Critical bond percolation measure on the square lattice](../../../../Probability/percolation/crossings/russo-seymour-welsh-theory/russo-seymour-welsh-bounds-for-critical-bond-per/critical-bond-measure.md)

## Expansion

Part 1 uses planar duality: a left-right open crossing of the strip exists unless a closed dual path joins its top and bottom borders, which needs a closed dual cluster of size at least $W$. Closed clusters are subcritical, so their sizes have exponential tails (Aizenman and Newman 1984); with $\alpha$ large, a union bound over the $d$ top-border nodes gives probability at most $1/d^2$, and a large finite open cluster is ruled out by Kesten's bound, so the crossing lies in $C^\infty$. For part 2 the walker works in phases, each time walking along a shortest path inside its ball to a node of the strip about $\beta \log d$ further to the right, for constants $\gamma \gg \beta \gg \alpha$. The Antal-Pisztora theorem (chemical distance in the cluster is at most a constant times the sup-norm distance, except with exponentially small probability) keeps the detour to the reference shortest path within $c\alpha \log d$, small compared with the $\beta \log d$ progress per phase, giving a factor $1 + \epsilon$ per phase and, by a union bound over at most $d$ phases, overall. Simulations in the source show that $\tilde D_\alpha$ is very close to the global shortest distance, so a logarithmic view suffices to navigate the maze almost optimally. This supports the interpretation of experiments in which ant groups carry a load through a random maze of cubes: in simulations of such transport, simulated walkers with an extended sensing range, like the ants, escape deep traps much better than walkers with very local sensing.

## Sources

- A. Gelblum, E. Fonio, Y. Rodeh, A. Korman and O. Feinerman, *Ant collective cognition allows for efficient navigation through disordered environments*, eLife 9 (2020), e55195. DOI: <https://doi.org/10.7554/eLife.55195>. PMCID: PMC7332297.
- P. Antal and A. Pisztora, *On the chemical distance for supercritical Bernoulli percolation*, Annals of Probability 24 (1996), 1036-1048.
- M. Aizenman and C. M. Newman, *Tree graph inequalities and critical behavior in percolation models*, Journal of Statistical Physics 36 (1984), 107-143.
