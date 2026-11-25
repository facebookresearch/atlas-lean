# Ergodic rate of mirror-prox

Throughout, $E$ is a real normed space, $E^*$ its dual with the dual norm $\|\cdot\|_*$, $Z \subseteq E$, $\omega$ a distance-generating function with derivative selection $\omega'$ and Bregman divergence $V$, strongly convex on $Z$ in the form $V_x(u) \ge \tfrac{\alpha}{2}\|u - x\|^2$ ($\alpha > 0$), and $F \colon E \to E^*$ an operator. Let $\gamma > 0$ with $\gamma L \le \alpha$, and let $F$ be monotone on $Z$, $(F(a) - F(b))(a - b) \ge 0$, and $L$-Lipschitz there, $\|F(a) - F(b)\|_* \le L\|a - b\|$. Let $z_t, w_t \in Z$ satisfy, for every $t$, the optimality conditions of the prox steps

$$
w_t = \operatorname{argmin}_{u \in Z}\{\gamma F(z_t)(u) + V_{z_t}(u)\}, \qquad z_{t+1} = \operatorname{argmin}_{u \in Z}\{\gamma F(w_t)(u) + V_{z_t}(u)\}.
$$

Then for $N \ge 1$ the average $\bar w_N = \frac{1}{N}\sum_{t<N} w_t$ satisfies, for every $u \in Z$,

$$
F(u)(\bar w_N - u) \le \frac{V_{z_0}(u)}{\gamma N} .
$$

The left-hand side, maximized over $u \in Z$, is the accuracy $\epsilon(\bar w_N)$ of $\bar w_N$ as a (weak) solution of the variational inequality: $\epsilon(z^\star) \le 0$ characterizes solutions. The proof telescopes the [one-step inequality](mirror-prox-step-le.md) and uses monotonicity, $F(u)(w_t - u) \le F(w_t)(w_t - u)$.

## Sources

- A. Nemirovski, *Prox-method with rate of convergence O(1/t) for variational inequalities with Lipschitz continuous monotone operators and smooth convex-concave saddle point problems*, SIAM J. Optim. 15(1) (2004), 229–251; author PDF at <https://www2.isye.gatech.edu/~nemirovs/SIOPT_042562-1.pdf>, Section 2, Proposition 2.2(ii), (2.13), with $\epsilon_t = 0$ (ensured by Lemma 3.1) and constant steps, for the iteration that always performs both prox steps (the iteration (4.2) of Section 4 with a constant step); here for every step with $\gamma L \le \alpha$.
