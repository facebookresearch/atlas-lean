# Minimum-variance rooting under random clock deviations

**Random deviations model.** Let $T_0$ be a rooted ultrametric tree of height $h$ with $n$ leaves and
root $r$. Generate $T$ by multiplying the length of each edge $(p(v), v)$ of $T_0$ by an independent
random factor $\alpha_v$ with support in $[1 - \epsilon, 1 + \epsilon]$ and $\mathbb{E}[\alpha_v] = 1$.
The true root of $T$ is the position $r$ inherited from $T_0$. Let $p$ be the global minimum-variance
(MV) root of the unrooted version of $T$, that is, the point minimizing the variance of root-to-tip
distances.

**Proposition (correct branch).** There is a threshold $\epsilon_0 > 0$, depending only on $n$, $h$, the
lengths $e_w$ of the edges from $r$ to its children $w$ and the clade sizes $|w|$, such that if
$\epsilon \le \epsilon_0$ then $p$ lies on an edge $(r, w)$ for some child $w$ of $r$.

**Proposition (unbiased position).** Whenever the global MV lies on an edge adjacent to $r$, the signed
distance $X$ from $r$ to the global MV along that edge satisfies $\mathbb{E}[X] = 0$.

**Corollary.** Under independent, bounded deviations from the strict molecular clock, MV rooting places
the root on the correct branch and, in expectation, at zero distance from the true root position on
that branch.

## Depends on

- [Local minimum-variance roots are balance points](local-minimum-variance-roots-are-balance-points.md)

## Expansion

With $\epsilon = 0$ the tree is ultrametric and the true root is the unique balance point. Small
multiplicative perturbations move the balance condition continuously, so for $\epsilon$ below a bound
set by the shortest root edge relative to the tree height the balance point cannot leave the edges
incident to $r$. On such an edge the MV position is the vertex of a quadratic whose coefficients are
linear in the perturbed edge lengths; since each factor has mean one, the perturbations of the two
group means cancel in expectation and the optimal displacement has mean zero. The model ignores rate
correlation along lineages and gene tree discordance, which is why the result motivates, rather than
guarantees, the method on real data; midpoint rooting has no comparable unbiasedness property because
it depends only on the two most distant leaves.

## Sources

- U. Mai, E. Sayyari, S. Mirarab, "Minimum variance rooting of phylogenetic trees and implications for
  species tree reconstruction", PLoS ONE 12 (2017) e0182238, Materials and methods, Propositions 4-5
  and Corollary 1, <https://doi.org/10.1371/journal.pone.0182238> (PMC5553649).
