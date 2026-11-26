# The genealogy-integrated likelihood

Coalescent likelihoods integrate the probability of the data given an unobserved genealogy against the coalescent law of the genealogy. In the formulation of Tavaré (2004, Section 6.7), $H$ is the history of a sample of $n$ chromosomes (its sequence of coalescence and mutation events back to the most recent common ancestor), $P_\theta(H)$ its law under the coalescent with mutation, and $q_\theta(D_n \mid H)$ the probability of the observed data $D_n$ given $H$, which equals $\prod_{\alpha \in E} n_\alpha!/n!$ when $H$ is consistent with $D_n$ and $0$ otherwise (equation (6.7.2)). The likelihood is

$$L(\theta) = q_\theta(D_n) = \int q_\theta(D_n \mid H)\, P_\theta(H)\, dH$$

(equation (6.7.4)). The naive Monte Carlo estimator $R^{-1}\sum_i q_\theta(D_n \mid H_i)$ with $H_i$ drawn from $P_\theta$ (equation (6.7.5)) is unbiased but useless in practice, because almost every simulated history is inconsistent with the data; this motivates importance sampling and Markov chain Monte Carlo. For sequence data with a mutation model acting on a tree with topology $\Lambda$ and times $T$, the factor given the genealogy is the product over sites of the single-site likelihoods computed by peeling, $P(D \mid \Lambda, T) = \prod_{i=1}^s L_i$, because sites evolve independently given the tree (Section 9.4, equation (9.4.1)).

## Expansion

1. The space of histories or genealogies with its coalescent law as a probability kernel in the demographic and mutation parameters.
2. The data kernel given a history: the consistency indicator with its combinatorial factor (6.7.2), and the peeling likelihood for sequence data (9.4.1).
3. The likelihood (6.7.4) as a composition of kernels, its measurability in $\theta$ and its normalization over data sets.
4. Which parameters enter which factor (for example, a mutation rate enters only the data kernel and a size history only the genealogy), and the factorization this gives.

## Sources

- S. Tavaré, Ancestral inference in population genetics, in *Lectures on Probability Theory and Statistics*, Lecture Notes in Math. 1837, Springer, 2004, 1–188, Sections 6.7 (equations (6.7.2), (6.7.4), (6.7.5)) and 9.4 (equation (9.4.1)).
