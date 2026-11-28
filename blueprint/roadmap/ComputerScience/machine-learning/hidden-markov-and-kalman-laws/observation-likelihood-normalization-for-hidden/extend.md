# Extending a finite observation string to a stream

For $t \in \mathbb{N}$ and an observation string $v = (v_0, \dots, v_t) \in O^{t+1}$, the extended stream $\bar v : \mathbb{N} \to O$ is

$$\bar v_i = \begin{cases} v_i & i \le t, \\ v_0 & i > t. \end{cases}$$

Only the values at $0, \dots, t$ matter for path weights and likelihoods of length $t + 1$.
