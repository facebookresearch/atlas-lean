# Back-door adjustment formula

Let $G$ be a directed acyclic graph on variables $V$, with joint law $P$ Markov with respect to $G$ and interventions defined by the [truncated factorization](../../../../../ComputerScience/machine-learning/probabilistic-graphical-models/causal-bayesian-networks/joint-mutilate-set.md): for disjoint $X$ and a value $x$, $P(v \mid \operatorname{do}(x))$ is obtained from $\prod_{V_i \in V} P(v_i \mid \mathrm{pa}_i)$ by deleting the factors of the variables in $X$ and setting $X = x$. Let $X, Y, Z$ be disjoint sets of variables. $Z$ satisfies the **back-door criterion** relative to $(X, Y)$ if

1. no node in $Z$ is a descendant of a node in $X$, and
2. $Z$ blocks every path between a node of $X$ and a node of $Y$ that contains an arrow into $X$ (in the sense of [$d$-separation](../../../../../ComputerScience/machine-learning/probabilistic-graphical-models/causal-bayesian-networks/dseparated.md)).

**Theorem.** If $Z$ satisfies the back-door criterion relative to $(X, Y)$ and $P(x, z) > 0$ wherever $P(z) > 0$, then

$$P(y \mid \operatorname{do}(x)) = \sum_{z} P(y \mid x, z)\, P(z).$$

## Expansion

Condition 1 makes $Z$ unaffected by the intervention, so $P(z \mid \operatorname{do}(x)) = P(z)$. Condition 2 means that, in the graph with the arrows out of $X$ removed, $Y$ and $X$ are $d$-separated by $Z$; hence the conditional law of $Y$ given $(x, z)$ is the same in the observational and the intervened distributions, $P(y \mid \operatorname{do}(x), z) = P(y \mid x, z)$. Summing over $z$ gives the formula. In potential-outcome language the criterion yields conditional ignorability $Y_x \perp X \mid Z$.

## Depends on

- [The truncated factorization for a set of nodes](../../../../../ComputerScience/machine-learning/probabilistic-graphical-models/causal-bayesian-networks/joint-mutilate-set.md)
- [d-separation](../../../../../ComputerScience/machine-learning/probabilistic-graphical-models/causal-bayesian-networks/dseparated.md)

## Sources

- J. Pearl, "Causal diagrams for empirical research", *Biometrika* 82 (1995), 669–688, <https://doi.org/10.1093/biomet/82.4.669>. The back-door criterion and its adjustment theorem; stated in the canonical form (full text not available; no theorem numbers cited).
