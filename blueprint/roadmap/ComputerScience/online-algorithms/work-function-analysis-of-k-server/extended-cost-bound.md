# Total extended cost is at most $2k \cdot \mathrm{OPT}$

For every $k$-server instance on any metric space, $\sum_{t=1}^T \mathrm{ext}_t \le 2k \cdot \mathrm{OPT}_T + c_1$ for all $T$, where $\mathrm{OPT}_T = \min_X w_T(X)$ and $c_1$ does not depend on the request sequence.

## Proof sketch

By the *duality lemma*, which follows from quasiconvexity, a configuration $A$ minimizing $w_{t-1}(X) - \sum_{a \in X} d(r_t, a)$ also minimizes $w_t(X) - \sum_{a \in X} d(r_t, a)$ and maximizes $w_t(X) - w_{t-1}(X)$, so $\mathrm{ext}_t = \min_X\big(w_t(X) - \sum_{x \in X} d(r_t, x)\big) - \min_X\big(w_{t-1}(X) - \sum_{x \in X} d(r_t, x)\big)$. Koutsoupias and Papadimitriou consider the potential

$$
\psi_t(A_0, b_0, \dots, A_{k-1}, b_{k-1}) = \sum_{i=0}^{k-1}\Big(w_t(A_i) - \sum_{a \in A_i} d(b_i, a)\Big) + k\, w_t(\{b_0, \dots, b_{k-1}\}).
$$

Using $w_t(B) = w_{t-1}(B - b_i + r_t) + d(b_i, r_t)$ for some $i$ and the triangle inequality, the minimum of $\psi_t$ is attained with some $b_i = r_t$; together with the duality lemma and the monotonicity of work functions in $t$ this gives $\min \psi_t - \min \psi_{t-1} \ge \mathrm{ext}_t$. Summing telescopes to $\min \psi_T$ up to an additive constant, and since $\psi_T$ contains $2k$ work-function values, each within a distance term of $\mathrm{OPT}_T$, $\min \psi_T \le 2k\,\mathrm{OPT}_T + \text{const}$.

## Depends on

- [Extended cost of a request](extended-cost.md)

## Proof depends on

- [Quasiconvexity of work functions](work-function-quasiconvexity.md)

## Sources

- Elias Koutsoupias, Christos H. Papadimitriou, "On the k-Server Conjecture", Journal of the ACM 42(5) (1995).
- Elias Koutsoupias, "The k-Server Problem", Computer Science Review 3(2) (2009), Lemma 1 and Theorem 3.
