# Uniform stability of RLM with a strongly convex regularizer

Let $E$ be a real inner product space, $K \subseteq E$ convex, $\ell : E \times Z \to \mathbb{R}$ a loss, $D$ a probability distribution on $Z$, and $A$ a regularized loss minimization (RLM) rule: on every sample $S \in Z^m$, $A(S)$ minimizes $L_S(w) + \mathcal{R}(w)$ over $w \in K$, where $L_S$ is the empirical risk. Write $S^{(i)}$ for $S$ with its $i$-th example replaced by a fresh $z'$, and assume the losses of the rule's outputs are integrable.
If $\mathcal{R}$ is $\sigma$-strongly convex on $K$ and every loss $\ell(\cdot, z)$ is convex on $K$, then for $u = A(S)$ and $v = A(S^{(i)})$,

$$
\sigma m \|v - u\|^2 \le \big(\ell(v, z_i) - \ell(u, z_i)\big) + \big(\ell(u, z') - \ell(v, z')\big).
$$

If moreover $\sigma > 0$ and every loss is $\rho$-Lipschitz on $K$, then $\|A(S) - A(S^{(i)})\| \le 2\rho/(\sigma m)$, so replacing one of $m$ examples changes the loss of the output on every example by at most $2\rho^2/(\sigma m)$.

## Proof sketch

Both regularized empirical objectives are $\sigma$-strongly convex, so each grows quadratically away from its own minimizer over $K$: $F_S(v) - F_S(u) \ge \frac{\sigma}{2}\|v-u\|^2$ and $F_{S^{(i)}}(u) - F_{S^{(i)}}(v) \ge \frac{\sigma}{2}\|v-u\|^2$. Adding the two and cancelling the common terms of the two objectives leaves exactly the two loss differences divided by $m$. With Lipschitz losses the right side is at most $2\rho\|v-u\|$.

## Depends on

- [Stability of regularized loss minimization](../../generalization-bounds-and-concentration/stability-of-regularized-loss-minimization.md)
- [On-average replace-one stability](../../generalization-bounds-and-concentration/algorithmic-stability/on-average-replace-one-stability.md)

## Sources

- S. Shalev-Shwartz and S. Ben-David, "Understanding Machine Learning: From Theory to Algorithms", Cambridge University Press, 2014.
- O. Bousquet and A. Elisseeff, "Stability and Generalization", Journal of Machine Learning Research, 2002.
