# Null expectation of the Jaccard coefficient

**Setting.** Let $y_i = (y_{i1}, \dots, y_{im})$ and $y_j = (y_{j1}, \dots, y_{jm})$ be binary presence–absence vectors over $m$ features (for example, the occurrence of two species across $m$ sites). Assume that the coordinates are independent, that $y_{ik} \sim \mathrm{Bernoulli}(p_i)$ and $y_{jk} \sim \mathrm{Bernoulli}(p_j)$ for every $k$, with $p_i, p_j \in (0,1)$, and that $y_i$ and $y_j$ are independent. Let

$$N_1 = \#\{k : y_{ik} = y_{jk} = 1\}, \quad N_2 = \#\{k : y_{ik} = 1, y_{jk} = 0\}, \quad N_3 = \#\{k : y_{ik} = 0, y_{jk} = 1\},$$

so that $(N_1, N_2, N_3, m - N_1 - N_2 - N_3)$ is multinomial with cell probabilities $p_i p_j$, $p_i(1-p_j)$, $(1-p_i)p_j$, $(1-p_i)(1-p_j)$. The Jaccard (Tanimoto) coefficient is

$$T(y_i, y_j) = \frac{N_1}{N_1 + N_2 + N_3},$$

with the convention $T(y_i, y_j) = \dfrac{p_i p_j}{p_i + p_j - p_i p_j}$ on the event $N_1 + N_2 + N_3 = 0$.

**Proposition.** Under independence,

$$\mathbb{E}\, T(y_i, y_j) = \frac{p_i p_j}{p_i + p_j - p_i p_j}.$$

Consequently the *centered* coefficient $T^c(y_i, y_j) = T(y_i, y_j) - \dfrac{p_i p_j}{p_i + p_j - p_i p_j}$ has mean zero under the null hypothesis of independent occurrence, whatever the occurrence probabilities.

## Proof depends on

- [Tower property of conditional expectation](../../../../Probability/foundations/conditional-expectation/tower-property/tower-property.md)

## Expansion

Condition on $S = N_1 + N_2 + N_3$. Given $S = s > 0$, each of the $s$ informative features is a joint presence independently with probability $p_i p_j / (p_i + p_j - p_i p_j)$, so $N_1 \mid S = s$ is binomial and $\mathbb{E}[N_1/S \mid S = s]$ equals that probability. The convention on $\{S = 0\}$ gives the same conditional mean, and the tower property finishes the proof. The raw coefficient therefore depends on the marginal occurrence rates even under independence, which is why tests use the centered version.

## Sources

- N. C. Chung, B. Miasojedow, M. Startek and A. Gambin, "Jaccard/Tanimoto similarity test and estimation methods for biological presence-absence data", *BMC Bioinformatics* (2019), Methods, Proposition 1. <https://doi.org/10.1186/s12859-019-3118-5> (PMC6929325)
