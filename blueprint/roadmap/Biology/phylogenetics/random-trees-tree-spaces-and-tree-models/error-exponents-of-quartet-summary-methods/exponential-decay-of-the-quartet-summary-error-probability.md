# Exponential decay of the quartet summary error probability

**Setting.** Let $N$ independent gene trees be generated on a fixed 4-taxon species tree by a gene evolution process that produces the correct unrooted topology with probability $p > 1/3$ and each of the two incorrect topologies with probability $(1-p)/2$. A quartet summary method (ASTRAL) returns the topology occurring most often among the gene trees, breaking ties uniformly. For $p \in (1/3, 1)$ define

$$c = \frac{1}{2 + \sqrt{(1-p)/(2p)}}, \qquad f(p) = -2c \ln c - (1 - 2c)\ln(1 - 2c) + c \ln p + (1 - c) \ln \frac{1-p}{2} \quad \text{(Equation 1)};$$

$f$ is negative on $(1/3, 1)$ and decreases monotonically.

**Theorem 1.** As $N \to \infty$, $\ln P(\text{error}) \sim f(p)\, N$.

**Theorem 3 (finite-$N$ bounds).** For every $N$, $\ln P(\text{error})$ is bounded below and above by $f$-type expressions $-2c'\ln c' - (1-2c')\ln(1-2c') + c'\ln p + (1-c')\ln\frac{1-p}{2}$ times $N$, with explicit $O(\ln N)$ and $O(1/N)$ corrections from a bounded Stirling formula, where $c'$ is the nearest number to $c$ with $c'N$ an integer.

**Theorem 6 (sample complexity under the multispecies coalescent).** If the internal branch of the species tree has length $l$ coalescent units, then $p = 1 - \tfrac23 e^{-l}$, and the minimum number of gene trees for ASTRAL to return the correct species tree with probability at least $1 - \epsilon$ satisfies, as $\epsilon \to 0$,

$$N \sim g(l) \ln \epsilon, \qquad g(l) = \frac{1}{f\big(1 - \tfrac23 e^{-l}\big)}, \qquad g(l) \sim -\tfrac43\, l^{-2} \ \ (l \to 0).$$

**Theorem 5 (many taxa).** For a species tree $S$ on $n$ taxa and a positively correlated gene evolution process (the multispecies coalescent is one), $\ln P(\text{error}) \sim \alpha N$ with

$$\max_x f(p_x)\, |A_x||B_x||C_x||D_x| \le \alpha \le f(p_{\min}),$$

where $x$ ranges over internal branches of $S$, $A_x, B_x, C_x, D_x$ are the four clades around $x$, $p_x$ is the correct-topology probability attached to $x$ in the paper's Equation (2), and $p_{\min}$ is the smallest correct-topology probability over all species quartets.

## Expansion

The counts $(N_1, N_2, N_3)$ of the three topologies are multinomial with probabilities $(p, \tfrac{1-p}{2}, \tfrac{1-p}{2})$. The method errs only if an incorrect topology ties or beats the correct one, and by Cramér-type large deviations the cheapest way is the boundary event $N_1 = N_2 = cN$, $N_3 = (1-2c)N$; maximizing the multinomial exponent $-2c\ln c - (1-2c)\ln(1-2c) + c\ln p + (1-c)\ln\frac{1-p}{2}$ over $c$ gives $\big((1-2c)/c\big)^2 = (1-p)/(2p)$, i.e. the stated $c$, and the value is $f(p)$. Setting $P(\text{error}) = \epsilon$ gives Theorem 6; for short branches $p - 1/3 \approx \tfrac23 l$ and $f(p) \approx -\tfrac34 l^2$. For more taxa, the upper bound uses that correct pluralities on all $\binom n4$ quartets suffice, while the lower bound counts the quartets spanning a single short branch.

## Sources

- Y.-b. Chan, Q. Li, C. Scornavacca, "The large-sample asymptotic behaviour of quartet-based summary methods for species tree inference", Journal of Mathematical Biology 85 (2022) 22, Equation (1), Theorems 1, 3, 5 and 6, <https://doi.org/10.1007/s00285-022-01786-4> (PMC9385842).
