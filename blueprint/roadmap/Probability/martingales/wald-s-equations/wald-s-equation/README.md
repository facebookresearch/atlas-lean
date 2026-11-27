# Wald's equation

Let $\mu$ be a probability measure, let $X_0, X_1, \dots$ be identically distributed real random variables with $X_0$ integrable, let $(\mathcal{F}_k)$ be a filtration such that each $X_k$ is independent of $\mathcal{F}_k$, and let $T$ be an $\mathbb{N}$-valued stopping time for $(\mathcal{F}_k)$ with $\mathbb{E}[T] < \infty$. Then the stopped sum $S_T = \sum_{i < T} X_i$ satisfies $\mathbb{E}[S_T] = \mathbb{E}[X_0]\, \mathbb{E}[T]$.

## Idea

If $T$ were independent of the $X_i$, the identity would follow by conditioning on $T$. Wald's equation allows the decision to stop to depend on the observations seen so far: whether $X_k$ enters the sum is decided by the event $\{T > k\}$, which lies in $\mathcal{F}_k$ and is therefore independent of $X_k$. Writing $S_T = \sum_k X_k \mathbf{1}_{\{T > k\}}$, each term has mean $\mathbb{E}[X_0]\, P(T > k)$, and $\sum_k P(T > k) = \mathbb{E}[T]$; the integrability of $T$ justifies exchanging sum and expectation. In sequential analysis this identity gives the expected number of observations a test needs.

## Statements

- [Wald's equation](wald-equation.md)
- [Integrability of the stopped sum in Wald's equation](wald-integrable-stopped-sum.md): basic property: the stopped sum is integrable

## Related topics

- [Sequential tests and quickest change detection](../../../hypothesis-testing/sequential-tests-and-quickest-change-detection/README.md): Wald's identity gives the average sample number of the sequential probability ratio test.
