# Ewens sampling formula

For a real number $\theta$ and an integer partition $\pi$ of $n$ with $a_j$ parts equal to $j$, let

$$E_\theta(\pi) = \frac{n!}{\theta(\theta + 1) \cdots (\theta + n - 1)} \prod_{j} \frac{(\theta/j)^{a_j}}{a_j!},$$

the product running over the part sizes $j$ of $\pi$, with the convention that division by $0$ gives $0$. For $\theta > 0$, it is the probability, under the neutral infinite-alleles model with scaled mutation rate $\theta = 4Nu$, that a sample of $n$ genes has allelic partition $\pi$: $a_j$ alleles carried by exactly $j$ genes each.

## Sources

- W. J. Ewens, *The sampling theory of selectively neutral alleles*, Theoret. Population Biol. 3 (1972), 87–112.
