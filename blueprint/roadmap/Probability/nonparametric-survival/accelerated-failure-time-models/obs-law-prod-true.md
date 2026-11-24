# Law of observed failures

Let the log failure time have law $\mu_T$ and the independent log censoring time law $\mu_C$, and observe $(Y, \delta) = (\min(\log T, \log C), \mathbf 1\{T \le C\})$. For measurable $A$, $P(Y \in A, \delta = 1) = \int_A\mu_C[t, \infty)\,d\mu_T(t)$.
