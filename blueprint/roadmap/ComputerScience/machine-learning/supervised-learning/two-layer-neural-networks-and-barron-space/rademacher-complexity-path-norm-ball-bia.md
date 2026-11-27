# Rademacher complexity of path-norm balls of two-layer ReLU networks with bias

Let $x_1, \dots, x_n \in \mathbb{R}^d$ have every coordinate in $[-1, 1]$, and let $Q \ge 0$. The
set of value vectors of the networks $f(x) = \sum_k a_k \max(\langle b_k, x \rangle + c_k, 0)$,
of any width, with $\sum_k \lvert a_k \rvert (\lVert b_k \rVert_1 + \lvert c_k \rvert) \le Q$, has
empirical Rademacher complexity at most $2 Q \sqrt{2 \log(2(d + 1)) / n}$.

It follows from the bound without bias in dimension $d + 1$, applied to the points
$(x_i, 1) \in \mathbb{R}^{d+1}$. This is the finite-width form of Theorem 6 of E, Ma and Wu
(*The Barron space and the flow-induced function spaces for neural network models*), whose proof
(§2.5.5) works with $\tilde x = (x, 1) \in \mathbb{R}^{d+1}$ and therefore yields
$\log(2(d+1))$; the statement of that theorem writes $\log(2d)$.

## Sources

- W. E, C. Ma and L. Wu, *The Barron space and the flow-induced function spaces for neural network models*, Constr. Approx. 55 (2022), Theorem 6 and its proof in §2.5.5 (data in $X = [0, 1]^d$; here $[-1, 1]^d$ is allowed).
