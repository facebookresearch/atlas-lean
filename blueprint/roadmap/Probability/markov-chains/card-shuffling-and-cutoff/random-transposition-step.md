# Step law of the random transposition shuffle

Let $n \in \mathbb{N}$. The step function of the random transposition shuffle on $n$ cards assigns to each permutation $\sigma$ of $\{1, \dots, n\}$ the number

$$\mu_n(\sigma) = \frac{\#\{(i, j) \in \{1, \dots, n\}^2 : (i\ j) = \sigma\}}{n^2},$$

where $(i\ i)$ is the identity and division by zero is read as $0$. For $n = 0$ there is a single permutation and no pair, and $\mu_0 = 0$. For $n > 0$, $\mu_n$ is the law of the transposition $(i\ j)$ of a uniform pair $(i, j)$: $\mu_n(\mathrm{id}) = 1/n$, $\mu_n(\tau) = 2/n^2$ for each transposition $\tau$, and $\mu_n = 0$ elsewhere (Diaconis and Shahshahani).
