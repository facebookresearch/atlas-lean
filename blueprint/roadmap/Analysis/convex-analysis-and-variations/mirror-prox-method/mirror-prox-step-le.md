# One-step inequality of mirror-prox

Throughout, $E$ is a real normed space, $E^*$ its dual with the dual norm $\|\cdot\|_*$, $Z \subseteq E$, $\omega$ a distance-generating function with derivative selection $\omega'$ and Bregman divergence $V$, strongly convex on $Z$ in the form $V_x(u) \ge \tfrac{\alpha}{2}\|u - x\|^2$ ($\alpha > 0$), and $F \colon E \to E^*$ an operator. Let $\gamma \ge 0$ and $z, w, z^+ \in Z$, where $w$ and $z^+$ satisfy the optimality conditions of the two prox steps

$$
w = \operatorname{argmin}_{u \in Z}\{\gamma F(z)(u) + V_z(u)\}, \qquad z^+ = \operatorname{argmin}_{u \in Z}\{\gamma F(w)(u) + V_z(u)\},
$$

and let $\gamma\|F(z) - F(w)\|_* \le \alpha\|z - w\|$ (true when $F$ is $L$-Lipschitz from $\|\cdot\|$ to $\|\cdot\|_*$ and $\gamma L \le \alpha$). Then for every $u \in Z$,

$$
\gamma\, F(w)(w - u) \le V_z(u) - V_{z^+}(u).
$$

The leading point $w$ is evaluated by the operator, and the update $z^+$ uses $F(w)$ from the old centre $z$; this "look-ahead" is what removes the error term $\gamma^2\|F\|_*^2$ of plain mirror descent. The proof applies the [three-point identity](../mirror-descent/bregman-three-point.md) twice and bounds the remainder $\gamma\|F(z) - F(w)\|_*\|w - z^+\| - \tfrac{\alpha}{2}(\|w - z\|^2 + \|w - z^+\|^2) \le 0$ directly; the source first bounds $\|w - z^+\| \le \gamma\|F(z) - F(w)\|_*/\alpha$, (3.7.a), which requires the smaller step $\gamma L \le \alpha/\sqrt{2}$.

## Background

- [One-step inequality of mirror descent](../mirror-descent/bregman-prox-step-le.md): the single-prox-step analogue, with the error term $\|\xi\|_*^2/(2\alpha)$.

## Sources

- A. Nemirovski, *Prox-method with rate of convergence O(1/t) for variational inequalities with Lipschitz continuous monotone operators and smooth convex-concave saddle point problems*, SIAM J. Optim. 15(1) (2004), 229–251; author PDF at <https://www2.isye.gatech.edu/~nemirovs/SIOPT_042562-1.pdf>, Section 3, Lemma 3.1, (3.7.b)–(3.7.d), with $U = Z$, $\xi = F(z)$, $\eta = F(w)$, where $H_u(z) - H_u(z^+) = V_z(u) - V_{z^+}(u)$.
