# Exponential decay from a one-step recursion

Let $d \in \mathbb{N}$, $p \in [0, 1]$, let $S \subseteq \mathbb{Z}^d$ be a finite set containing the origin with $\varphi_p(S) < 1$, and let $L \ge 1$. Write $\theta_n(p)$ for the [one-arm probability](cross-prob.md). If

$$\theta_{(k+1)L}(p) \le \varphi_p(S)\, \theta_{kL}(p) \quad \text{for all } k \in \mathbb{N},$$

then there are $c, C > 0$ with $\theta_n(p) \le C e^{-cn}$ for all $n \in \mathbb{N}$.
