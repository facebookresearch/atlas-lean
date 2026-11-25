# Closed-form law of the Chinese restaurant process

For a real number $\theta$ and a set partition $\pi$ of $\{0, \dots, n-1\}$, let

$$p_\theta(\pi) = \frac{\theta^{|\pi|} \prod_{B \in \pi} (|B| - 1)!}{\theta(\theta + 1) \cdots (\theta + n - 1)},$$

with the convention that division by $0$ gives $0$; every block is nonempty, so $|B| - 1 \ge 0$.

## Sources

- J. Pitman, *Combinatorial Stochastic Processes*, Lecture Notes in Math. 1875, Springer (2006), §3.1.
