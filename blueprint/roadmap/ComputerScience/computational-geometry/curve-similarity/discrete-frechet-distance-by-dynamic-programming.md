# Discrete Fréchet distance by dynamic programming

Let $\pi = (p_1, \dots, p_n)$ and $\sigma = (q_1, \dots, q_m)$ be nonempty sequences of points in $\mathbb{R}^d$, for fixed $d$, and let $f(x, y)$ be the discrete Fréchet distance between $(p_1, \dots, p_x)$ and $(q_1, \dots, q_y)$. Then $f(1,1) = \|p_1 - q_1\|$ and, for $(x, y) \ne (1, 1)$,

$$f(x, y) = \max\big(\|p_x - q_y\|, \min(f(x-1, y), f(x, y-1))\big),$$

with $f(0, y) = f(x, 0) = \infty$. Filling the table computes $d_F(\pi, \sigma) = f(n, m)$ and a walk realizing it in $O(nm)$ time.

## Depends on

- [Discrete Fréchet distance](discrete-frechet-distance.md)

## Sources

- S. Har-Peled, *Geometric Approximation Algorithms*, revised online chapter "Fréchet distance: How to walk your dog" (Chapter 33), <https://sarielhp.org/book/chapters/frechet.pdf>: Section 33.1.2.1, the recurrence for $f(x, y)$, and Lemma 33.1.3 ($O(nm)$ time)
