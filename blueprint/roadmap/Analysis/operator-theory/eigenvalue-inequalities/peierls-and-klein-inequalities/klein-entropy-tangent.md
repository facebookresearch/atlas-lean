# Entropy tangent bound in an arbitrary orthonormal basis

Let $E$ be a complex inner product space of finite dimension $n$, let $T$ and $S$ be self-adjoint operators on $E$ with eigenvalues $\mu_0 \ge \dots \ge \mu_{n-1}$ and $\lambda_0 \ge \dots \ge \lambda_{n-1}$ respectively (repeated according to multiplicity), and let $(b_i)_{i < n}$ be an orthonormal basis of $E$. Assume $\operatorname{Re} \langle x, T x \rangle \ge 0$ for every $x$ and $\operatorname{Re} \langle x, S x \rangle > 0$ for every $x \ne 0$, and put $t_i = \operatorname{Re} \langle b_i, T b_i \rangle$. Then, with the convention $0 \log 0 = 0$,

$$
\sum_{i=0}^{n-1} \big( \lambda_i \log \lambda_i + (\log \lambda_i + 1)(t_i - \lambda_i) \big) \le \sum_{j=0}^{n-1} \mu_j \log \mu_j.
$$

The basis need not be an eigenbasis of $S$; [Klein's entropy inequality](klein-entropy.md) is the case of the eigenbasis of $S$.
