# Kinship coefficient

In an [identity-by-descent model](ibdmodel.md), the kinship coefficient of individuals $i$ and $j$ is

$$\varphi_{ij} = \frac{1}{4} \sum_{a, b \in \{0, 1\}} \mathrm{ibd}\bigl((i, a), (j, b)\bigr),$$

when the values $\mathrm{ibd}$ are genuine identity-by-descent probabilities (in $[0, 1]$, as in Malécot's model), it is the probability that a copy drawn at random from $i$ and a copy drawn at random from $j$ are identical by descent.
