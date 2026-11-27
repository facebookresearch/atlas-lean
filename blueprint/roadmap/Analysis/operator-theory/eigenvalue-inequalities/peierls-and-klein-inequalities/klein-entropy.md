# Klein's entropy inequality

Let $E$ be a complex inner product space of finite dimension $n$, let $T$ and $S$ be self-adjoint operators on $E$ with eigenvalues $\mu_0 \ge \dots \ge \mu_{n-1}$ and $\lambda_0 \ge \dots \ge \lambda_{n-1}$, and let $(e_i)$ be an orthonormal eigenbasis of $S$ with $S e_i = \lambda_i e_i$. Assume $\operatorname{Re} \langle x, T x \rangle \ge 0$ for every $x$ and $\operatorname{Re} \langle x, S x \rangle > 0$ for every $x \ne 0$. Then, with the convention $0 \log 0 = 0$,

$$
\sum_{i=0}^{n-1} \big( \lambda_i \log \lambda_i + (\log \lambda_i + 1)(\operatorname{Re} \langle e_i, T e_i \rangle - \lambda_i) \big) \le \sum_{j=0}^{n-1} \mu_j \log \mu_j.
$$

The left side is $\operatorname{tr}(T \log S) + \operatorname{tr} T - \operatorname{tr} S$, so this is the relative entropy inequality $\operatorname{tr}(T \log T - T \log S) \ge \operatorname{tr}(T - S)$; the correction term vanishes when $T = S$.
