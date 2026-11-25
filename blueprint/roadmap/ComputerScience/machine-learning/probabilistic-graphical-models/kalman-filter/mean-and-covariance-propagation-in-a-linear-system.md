# Mean and covariance propagation in a linear system with uncorrelated noise

Let $A \in \mathbb{R}^{n \times n}$ and $B \in \mathbb{R}^{n \times m}$, let $(u(k))_{k \ge 0}$ be a deterministic input sequence in $\mathbb{R}^m$, and let $x(0), w(0), w(1), \dots$ be random vectors in $\mathbb{R}^n$ on one probability space, each with finite second moments. Define

$$x(k+1) = A x(k) + B u(k) + w(k), \qquad k \ge 0.$$

Assume that for every $k$ the noise $w(k)$ is uncorrelated with $x(0)$ and with $w(j)$ for every $j < k$, that is, $\operatorname{Cov}(w(k), x(0)) = 0$ and $\operatorname{Cov}(w(k), w(j)) = 0$. Write $m(k) = \mathbb{E}[x(k)]$, $P(k) = \operatorname{Cov}(x(k))$ and $Q_k = \operatorname{Cov}(w(k))$. Then for every $k \ge 0$:

1. $m(k+1) = A\, m(k) + B\, u(k) + \mathbb{E}[w(k)]$;
2. $\operatorname{Cov}(x(k), w(k)) = 0$;
3. $P(k+1) = A\, P(k)\, A^\top + Q_k$.

In particular, for zero-mean noise $m(k+1) = A m(k) + B u(k)$. With $u = 0$ and $w(k) = G_k \tilde w(k)$, where $\operatorname{Cov}(\tilde w(k)) = \tilde Q_k$, so that $Q_k = G_k \tilde Q_k G_k^\top$, these are the state statistics of the Gauss–Markov model with constant $F_k = A$.

**Proof.** By induction, $x(k) = A^k x(0) + \sum_{j < k} A^{k-1-j} \big(B u(j) + w(j)\big)$, which is a deterministic vector plus a linear combination of $x(0), w(0), \dots, w(k-1)$, so $x(k)$ has finite second moments. Part 1 is linearity of expectation. Covariance is bilinear and vanishes against deterministic vectors, so the hypotheses give $\operatorname{Cov}(x(k), w(k)) = A^k \operatorname{Cov}(x(0), w(k)) + \sum_{j < k} A^{k-1-j} \operatorname{Cov}(w(j), w(k)) = 0$, which is part 2. Then

$$P(k+1) = A P(k) A^\top + A \operatorname{Cov}(x(k), w(k)) + \operatorname{Cov}(w(k), x(k)) A^\top + Q_k = A P(k) A^\top + Q_k .$$

## Background

- [The predict step is exact](map-predict.md): the one-step Gaussian case with independent noise, where $F x + w$ has the law $N(F m, F P F^\top + Q)$

## Sources

- B. D. O. Anderson and J. B. Moore, *Optimal Filtering*, Prentice-Hall, 1979, <https://users.cecs.anu.edu.au/~john/papers/BOOK/B02.PDF>, Section 2.2, the state statistics of the Gauss–Markov model $x_{k+1} = F_k x_k + G_k w_k$ with independent zero-mean noise: $\bar{x}_{k+1} = F_k \bar{x}_k$ and $P_{k+1} = F_k P_k F_k^\top + G_k Q_k G_k^\top$ ((2.20), p. 20, and the summary on p. 21), with the remark on p. 21 that the mean and covariance formulas remain valid without the Gaussian assumption, and Problem 2.4 (p. 22), nonzero known noise means, as an exercise. Here only second moments and uncorrelatedness, rather than independence, are assumed, and the noise mean and the input are kept; the proof is on the page.
