# Exponential polynomials that do not decay are not integrable

Let $\lambda_1, \dots, \lambda_r \in \mathbb{C}$ be distinct and let $p_1, \dots, p_r$ be complex polynomials.

1. **Continuous time.** If $p_j \ne 0$ for some $j$ with $\operatorname{Re} \lambda_j \ge 0$, then $f(t) = \sum_{i=1}^r p_i(t)\, e^{\lambda_i t}$ is not integrable on $[0, \infty)$: $\int_0^\infty |f(t)|\, dt = \infty$.
2. **Discrete time.** If $p_j \ne 0$ for some $j$ with $|\lambda_j| \ge 1$, then $g(k) = \sum_{i=1}^r p_i(k)\, \lambda_i^k$ is not summable: $\sum_{k \ge 0} |g(k)| = \infty$.

Conversely, if every $\lambda_i$ with $p_i \ne 0$ has negative real part (respectively modulus less than $1$), $f$ is integrable (respectively $g$ is summable). So the entries of $C e^{tA} B$ and of $C A^k B$, which have these forms (in discrete time up to finitely many initial terms when $A$ is not invertible), are integrable or summable exactly when no eigenvalue with nonzero coefficient lies in the closed right half-plane or outside the open unit disc.

**Proof.** For part 1, suppose $f$ is integrable. Its one-sided Laplace transform $F(s) = \int_0^\infty f(t) e^{-st}\, dt$ is then defined, bounded by $\int_0^\infty |f|$, and holomorphic on $\{\operatorname{Re} s > 0\}$. Writing $p_i(t) = \sum_k c_{ik} t^k$ and using $\int_0^\infty t^k e^{-(s - \lambda)t}\, dt = k!/(s - \lambda)^{k+1}$ for $\operatorname{Re} s > \operatorname{Re} \lambda$, for $\operatorname{Re} s > \max_i \operatorname{Re} \lambda_i$

$$F(s) = R(s) = \sum_{i=1}^r \sum_k \frac{c_{ik}\, k!}{(s - \lambda_i)^{k+1}},$$

a rational function holomorphic off $\{\lambda_1, \dots, \lambda_r\}$. Both $F$ and $R$ are holomorphic on the connected open set $\{\operatorname{Re} s > 0\} \setminus \{\lambda_1, \dots, \lambda_r\}$ and agree on a half-plane inside it, so they agree on all of it. Near $\lambda_j$ the terms with $i \ne j$ are holomorphic, and the principal part $\sum_k c_{jk} k!/(s - \lambda_j)^{k+1}$ is nonzero because $p_j \ne 0$, so $|R(s)| \to \infty$ as $s \to \lambda_j$. Taking $s = \lambda_j + \varepsilon$ with $\varepsilon \downarrow 0$, which lies in $\{\operatorname{Re} s > 0\}$ and avoids the other $\lambda_i$ for small $\varepsilon$, contradicts the bound on $F$. Part 2 is the same argument with the z-transform $G(z) = \sum_{k \ge 0} g(k) z^{-k}$, which is bounded on $\{|z| \ge 1\}$ and holomorphic on $\{|z| > 1\}$ if $g$ is summable; each $\sum_{k} k^m \lambda^k z^{-k}$ with $\lambda \ne 0$ is a rational function of $z$ whose only pole is at $\lambda$, of order $m + 1$, and one approaches $\lambda_j$ along $z = \lambda_j(1 + \varepsilon)$. For the converse, $|t^k e^{\lambda t}| \le C_\delta e^{(\operatorname{Re}\lambda + \delta)t}$ for every $\delta > 0$, and similarly for $k^m \lambda^k$.

## Sources

- E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., Texts in Applied Mathematics 6, Springer, 1998, <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>, Section 7.3, proof of Proposition 7.3.3 (p. 328): the entries of $C e^{tA} B$ are sums of terms $t^l e^{\lambda t}$ over eigenvalues $\lambda$, integrable when every real part is negative, and in discrete time the entries of $CA^{i-1}B$ are sums of terms $t^l\lambda^i$ with $|\lambda| < 1$. The non-integrability direction and its Laplace-transform proof are derived on the page.
