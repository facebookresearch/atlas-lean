# Randomized voting rules cannot beat metric distortion 2.112

There is a constant $\delta^* > 2.112$ such that every randomized voting rule has metric distortion at least $\delta^*$, when the numbers of voters and candidates may be arbitrarily large. The lower bounds for $m$ candidates are about $2.0261$ for $m = 3$, $2.0496$ for $m = 4$, and tend to about $2.1126$ as $m \to \infty$. In particular the long-standing conjecture that distortion $2$ is achievable by randomized rules is false.

## Proof sketch

Restrict the adversary to a simple class of metrics, the biased metrics, which are described by few parameters, and construct elections in which, for every distribution over candidates, some biased metric consistent with the rankings makes the expected social cost large compared with the optimum. On this class the worst-case ratio of the best randomized rule is the value of an explicit optimization problem, whose value for $m$ candidates increases with $m$ towards about $2.1126$. For three candidates a matching upper bound holds on this restricted class.

## Depends on

- [Metric election and distortion of a voting rule](metric-election-and-distortion.md)

## Sources

- M. Charikar, P. Ramakrishnan, "Metric Distortion Bounds for Randomized Social Choice", SODA 2022, arXiv:2111.03694.
