# Probability raising, positive dependence and temporal priority

**Setting.** Let $i$ and $j$ be binary events (for example, the presence of two somatic alterations in a tumour sample) on a probability space, with marginal probabilities $p_i = P(i)$, $p_j = P(j)$ and joint probability $p_{ij} = P(i \cap j)$. Assume $0 < p_i < 1$ and $0 < p_j < 1$, so that all conditional probabilities below are defined. Event $i$ is a **probability raiser** of $j$ if

$$P(j \mid i) > P(j \mid \bar{i}).$$

**Proposition (dependency).** $i$ raises the probability of $j$ if and only if $i$ and $j$ are positively dependent, $p_{ij} > p_i\,p_j$.

**Proposition (mutual probability raising).** $P(j \mid i) > P(j \mid \bar i)$ if and only if $P(i \mid j) > P(i \mid \bar j)$.

**Proposition (probability raising and temporal priority).** Suppose $p_{ij} > p_i p_j$ and $p_{ij} < \min(p_i, p_j)$. Then

$$\frac{P(j \mid i)}{P(j \mid \bar i)} > \frac{P(i \mid j)}{P(i \mid \bar j)} \quad\Longleftrightarrow\quad p_i > p_j .$$

Thus, among two positively dependent events, the more frequent one raises the probability of the other more strongly. Reading event frequency as a proxy for time of occurrence (a cause precedes, hence is observed at least as often as, its effect in a tree-structured accumulation process), this motivates the definition: $i$ is a **prima facie cause** of $j$ if $i$ is a probability raiser of $j$ and $p_i > p_j$.

## Expansion

Dependency: $P(j\mid i) = p_{ij}/p_i$ and $P(j\mid \bar i) = (p_j - p_{ij})/(1-p_i)$. The inequality $p_{ij}(1-p_i) > p_i(p_j - p_{ij})$ simplifies to $p_{ij} > p_i p_j$. Mutual probability raising follows because this condition is symmetric in $i$ and $j$.

Temporal priority: write $r_{i\to j} = P(j\mid i)/P(j\mid\bar i) = \frac{p_{ij}(1-p_i)}{p_i(p_j - p_{ij})}$ and symmetrically $r_{j\to i} = \frac{p_{ij}(1-p_j)}{p_j(p_i-p_{ij})}$. Clearing the positive denominators, $r_{i\to j} > r_{j\to i}$ is equivalent to $(1-p_i)p_j(p_i - p_{ij}) > (1-p_j)p_i(p_j - p_{ij})$, and expanding both sides the difference equals

$$(p_i - p_j)(p_{ij} - p_i p_j).$$

Under positive dependence the second factor is positive, so the sign is that of $p_i - p_j$.

The paper uses these facts to justify orienting each candidate edge from the more frequent to the less frequent event; spurious causes (a common ancestor of both events) are not excluded by probability raising alone, which is why a further filter is needed in tree reconstruction.

## Sources

- L. Olde Loohuis, G. Caravagna, A. Graudenzi, D. Ramazzotti, G. Mauri, M. Antoniotti, B. Mishra, "Inferring tree causal models of cancer progression with probability raising", PLoS ONE 9(10) (2014) e108358, Definitions 2–3 and Propositions 1–3, <https://doi.org/10.1371/journal.pone.0108358>, PMCID PMC4191986.
- P. Suppes, *A Probabilistic Theory of Causality*, North-Holland, Amsterdam, 1970.
