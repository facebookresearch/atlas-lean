# Step law of the random transposition shuffle

Let $n \in \mathbb{N}$. The step law of the random transposition shuffle on $n$ cards is the probability function on permutations $\sigma$ of $\{1, \dots, n\}$

$$\mu_n(\sigma) = \frac{\#\{(i, j) \in \{1, \dots, n\}^2 : (i\ j) = \sigma\}}{n^2},$$

the law of the transposition $(i\ j)$ of a uniform pair $(i, j)$, where $(i\ i)$ is the identity. So $\mu_n(\mathrm{id}) = 1/n$, $\mu_n(\tau) = 2/n^2$ for each transposition $\tau$, and $\mu_n = 0$ elsewhere (Diaconis and Shahshahani).
