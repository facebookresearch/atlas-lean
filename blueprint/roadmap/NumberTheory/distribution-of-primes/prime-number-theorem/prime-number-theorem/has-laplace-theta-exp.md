# Convergence of the Laplace transform of $\theta(e^t)$

Let
$\theta(x) = \sum_{p \le x} \log p$ be Chebyshev's function, the sum running over the primes
$p \le x$. For every $s \in \mathbb{C}$ with $\operatorname{Re} s > 1$, the function
$t \mapsto \theta(e^t)$ has Laplace transform $\frac{1}{s} \sum_p \log p \cdot p^{-s}$ at $s$,
where the sum runs over all primes $p$ (this is the prime logarithm series at $s$ divided by
$s$): the function $t \mapsto e^{-st}\,\theta(e^t)$ is integrable on $(0, \infty)$ and its
integral over $(0, \infty)$ equals $\frac{1}{s} \sum_p \log p \cdot p^{-s}$.

## Sources

- A. V. Sutherland, *Number theory I* (MIT 18.785), lecture notes, Fall 2021, Lecture 16, Lemma 16.10, https://math.mit.edu/classes/18.785/2021fa/LectureNotes16.pdf.
