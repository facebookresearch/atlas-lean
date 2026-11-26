# Mirror-prox method

The mirror-prox method (Nemirovski, 2004) solves variational inequalities with a monotone Lipschitz operator $F$ on a convex set $Z$, which include convex-concave saddle-point problems such as matrix games, at the rate $O(1/N)$. Each step makes two prox steps of [mirror descent](../mirror-descent/README.md) from the same centre $z_t$: a leading step $w_t$ with $F(z_t)$, then the update $z_{t+1}$ with $F(w_t)$. The [one-step inequality](mirror-prox-step-le.md) has no error term once $\gamma L \le \alpha$, so the average of the leading points satisfies the [ergodic bound](mirror-prox-average-le.md) $F(u)(\bar w_N - u) \le V_{z_0}(u)/(\gamma N)$, and with Nemirovski's step the [efficiency estimate](mirror-prox-average-le-sqrt-two.md) $\sqrt{2}\Theta L/(\alpha N)$. For a convex-concave $f$ and $F = (\partial_x f, -\partial_y f)$ the same bound controls the [saddle-point gap](mirror-prox-saddle-le-sqrt-two.md) of the averaged leading points. In the Euclidean setup it is Korpelevich's extragradient method. As for mirror descent, prox steps are used through their optimality conditions and strong convexity in the Bregman form.

- [One-step inequality of mirror-prox](mirror-prox-step-le.md)
- [Ergodic rate of mirror-prox](mirror-prox-average-le.md)
- [The $O(1/N)$ rate of mirror-prox with the step $\alpha / (\sqrt{2} L)$](mirror-prox-average-le-sqrt-two.md)
- [Telescoped mirror-prox bound](mirror-prox-sum-le.md)

## Saddle-point problems

- [Mirror-prox for convex-concave saddle points](mirror-prox-saddle-le.md)
- [The $O(1/N)$ saddle-point accuracy of mirror-prox with the step $\alpha / (\sqrt{2} L)$](mirror-prox-saddle-le-sqrt-two.md)

## Related topics

- [Mirror descent](../mirror-descent/README.md): the proximal setup and the Bregman divergence; mirror descent for nonsmooth problems has rate $O(1/\sqrt{N})$.
- [Stampacchia's theorem](../stampacchia-s-theorem/README.md): existence and uniqueness for variational inequalities with coercive bilinear forms, the existence side of the problems mirror-prox solves.
- [Von Neumann's minimax theorem](../../../GameTheory/noncooperative-games/von-neumann-s-minimax-theorem/README.md): matrix games, bilinear saddle-point problems over pairs of simplices, are the first application of mirror-prox in Nemirovski (2004), Section 5, Example 1.
