# Laplace transform of $\theta(e^t)$

Let $\theta(x) = \sum_{p \le x} \log p$ be
Chebyshev's function, the sum running over the primes $p \le x$. For every $s \in \mathbb{C}$
with $\operatorname{Re} s > 1$, the Laplace transform
$\int_{(0, \infty)} e^{-st}\,\theta(e^t)\,dt$ of $t \mapsto \theta(e^t)$ at $s$ equals
$\frac{1}{s} \sum_p \log p \cdot p^{-s}$, the prime logarithm series at $s$ divided by $s$,
where the sum runs over all primes $p$.

## Sources

- A. V. Sutherland, *Number theory I* (MIT 18.785), lecture notes, Fall 2021, Lecture 16, Lemma 16.10, https://math.mit.edu/classes/18.785/2021fa/LectureNotes16.pdf.
