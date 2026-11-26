# Randomized voting rules cannot beat metric distortion 2.112

There is a constant $\delta^* > 2.112$ such that every randomized voting rule has metric distortion at least $\delta^*$, when the numbers of voters and candidates may be arbitrarily large. In particular the long-standing conjecture that distortion $2$ is achievable by randomized rules is false.

## Proof sketch

Construct a family of profiles with a high-dimensional symmetric structure of candidates and voters in which any distribution over candidates must place weight on a candidate far from the optimum for some consistent metric. Exploiting symmetry, the best randomized rule on this family is described by a small number of parameters, and the worst-case ratio reduces to a one-dimensional optimization whose value is approximately $2.1126$.

## Depends on

- [Metric election and distortion of a voting rule](metric-election-and-distortion.md)

## Proof depends on

- [Random dictatorship has metric distortion 3 - 2/n](random-dictatorship-distortion.md)

## Sources

- M. Charikar, P. Ramakrishnan, "Metric Distortion Bounds for Randomized Social Choice", SODA 2022, arXiv:2111.03694.
