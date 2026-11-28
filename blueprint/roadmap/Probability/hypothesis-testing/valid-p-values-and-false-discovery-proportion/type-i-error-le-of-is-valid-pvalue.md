# Type I error of a p-value rejection rule

Let $\mu$ be a measure on $\Omega$, not necessarily finite, with values $\mu(A) \in [0, \infty]$, and write $\mu_{\mathbb{R}}(A) \in [0, \infty)$ for its real-valued mass, equal to $\mu(A)$ when $\mu(A) < \infty$ and to $0$ when $\mu(A) = \infty$. A p-value $p$ is valid under $\mu$ if $\mu(p \le t) \le t$ in $[0, \infty]$ for every $t \in [0, 1]$. If $p$ is valid under $\mu$ and $\alpha \in [0, 1]$, then rejecting when $p \le \alpha$ has type I error at most $\alpha$: $\mu_{\mathbb{R}}(p \le \alpha) \le \alpha$.

The hypothesis must use the extended mass. Read with real-valued masses it would be weaker: on a one-point space of infinite mass, the constant p-value $0$ has $\mu_{\mathbb{R}}(p \le t) = 0 \le t$ for every $t \in [0, 1]$, although $\mu(p \le t) = \infty$, so it is not valid.
