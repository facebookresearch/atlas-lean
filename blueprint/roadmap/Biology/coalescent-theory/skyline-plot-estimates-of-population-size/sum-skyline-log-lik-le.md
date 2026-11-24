# The skyline estimates jointly maximize the likelihood

Let $s$ be a finite set of intervals and $c_i$, $w_i$, $\theta_i$ positive real numbers for $i \in s$. Then

$$\sum_{i \in s} \ell_{c_i, w_i}(\theta_i) \le \sum_{i \in s} \ell_{c_i, w_i}(c_i w_i),$$

where $\ell_{c,w}$ is the [interval log-likelihood](skyline-log-lik.md) with parameters $c$ and $w$.
