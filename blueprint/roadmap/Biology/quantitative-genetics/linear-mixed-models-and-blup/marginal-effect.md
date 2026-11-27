# Marginal association estimate of a marker

For a real $N \times M$ genotype matrix $X$, fixed effects $\beta \in \mathbb{R}^M$ and noise functions $\varepsilon_1, \dots, \varepsilon_N$ on $\Omega$, the marginal estimate of marker $j$ is the function

$$\hat\beta_j = \frac{1}{N} \sum_{i=1}^{N} X_{ij} \Bigl(\sum_{k=1}^{M} X_{ik} \beta_k + \varepsilon_i\Bigr),$$

with the convention $x/0 = 0$ when $N = 0$.
