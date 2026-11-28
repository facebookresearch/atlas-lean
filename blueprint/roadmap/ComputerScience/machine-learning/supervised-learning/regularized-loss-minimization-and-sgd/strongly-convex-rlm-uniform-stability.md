# Uniform stability of RLM with a strongly convex regularizer

Let $E$ be a real inner product space, $K \subseteq E$ convex, $\ell : E \times Z \to \mathbb{R}$ a loss, $D$ a probability distribution on $Z$, and $A$ a regularized loss minimization (RLM) rule: on every sample $S \in Z^m$, $A(S)$ minimizes $L_S(w) + \mathcal{R}(w)$ over $w \in K$, where $L_S$ is the empirical risk. Write $S^{(i)}$ for $S$ with its $i$-th example replaced by a fresh $z'$, and assume the losses of the rule's outputs are integrable.
For the strongly convex Tikhonov regularizer $\mathcal{R}(w) = \lambda\|w\|^2$ with $\lambda > 0$ and every loss $\ell(\cdot, z)$ convex on $K$, for $u = A(S)$ and $v = A(S^{(i)})$,

$$
\lambda \|v - u\|^2 \le \frac{\ell(v, z_i) - \ell(u, z_i)}{m} + \frac{\ell(u, z') - \ell(v, z')}{m}
$$

(Shalev-Shwartz and Ben-David, Equation (13.10)). If moreover every loss is $\rho$-Lipschitz on $K$, then $\|A(S) - A(S^{(i)})\| \le 2\rho/(\lambda m)$, so replacing one of $m$ examples changes the loss of the output on the replaced example by at most $2\rho^2/(\lambda m)$, for every $S$, $z'$ and $i$, and the rule is on-average-replace-one-stable with rate $2\rho^2/(\lambda m)$ (Section 13.3.1 and Corollary 13.6).

## Proof sketch

The objective $f_S(w) = L_S(w) + \lambda\|w\|^2$ is $2\lambda$-strongly convex, so $f_S(v) - f_S(u) \ge \lambda\|v - u\|^2$; since $v$ minimizes the objective of $S^{(i)}$, the difference $f_S(v) - f_S(u)$ is at most the two loss differences divided by $m$ (Equations (13.7) to (13.10)). With Lipschitz losses the right side is at most $2\rho\|v-u\|/m$.

Derived (not stated in the cited sources): for any regularizer $\mathcal{R}$ that is $\sigma$-strongly convex on $K$, each of the two regularized empirical objectives grows quadratically away from its own minimizer over $K$, $F_S(v) - F_S(u) \ge \frac{\sigma}{2}\|v-u\|^2$ and $F_{S^{(i)}}(u) - F_{S^{(i)}}(v) \ge \frac{\sigma}{2}\|v-u\|^2$; adding the two and cancelling the common terms gives $\sigma m \|v - u\|^2 \le (\ell(v, z_i) - \ell(u, z_i)) + (\ell(u, z') - \ell(v, z'))$, and with $\rho$-Lipschitz losses and $\sigma > 0$, $\|A(S) - A(S^{(i)})\| \le 2\rho/(\sigma m)$ and every loss of the output changes by at most $2\rho^2/(\sigma m)$.

## Depends on

- [Stability of regularized loss minimization](../../generalization-bounds-and-concentration/stability-of-regularized-loss-minimization.md)
- [On-average replace-one stability](../../generalization-bounds-and-concentration/algorithmic-stability/on-average-replace-one-stability.md)

## Sources

- S. Shalev-Shwartz and S. Ben-David, "Understanding Machine Learning: From Theory to Algorithms", Cambridge University Press, 2014, Section 13.3, Equations (13.7) to (13.10) and Corollary 13.6.
- O. Bousquet and A. Elisseeff, "Stability and Generalization", Journal of Machine Learning Research, 2002.
