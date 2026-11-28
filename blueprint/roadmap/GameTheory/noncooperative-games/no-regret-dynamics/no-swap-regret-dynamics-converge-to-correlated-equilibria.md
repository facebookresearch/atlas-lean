# No-swap-regret dynamics converge to correlated equilibria

Let players repeatedly play a finite game for $T \ge 1$ rounds, with realized profiles $s^1, \dots, s^T$ and payoffs $u_i = -c_i$, and let player $i$'s
average swap regret be $\max_{\phi} \frac1T \sum_t (u_i(\phi(s_i^t), s_{-i}^t) - u_i(s^t))$ over maps $\phi$ from $i$'s strategies to $i$'s strategies. Call a
distribution $\sigma$ on profiles a swap $\varepsilon$-correlated equilibrium if, for every player $i$ and every $\phi$,
$\mathbb{E}_{s \sim \sigma}[u_i(\phi(s_i), s_{-i}) - u_i(s)] \le \varepsilon$ (unconditioned incentive constraints). If every player's average swap regret is at most
$\varepsilon$, the empirical distribution of play is a swap $\varepsilon$-correlated equilibrium; the same holds for the time average of the product
distributions when each player's expected swap regret against the others' mixed strategies is at most $\varepsilon$. A swap $\varepsilon$-correlated
equilibrium is a correlated $\varepsilon$-equilibrium in the sense of the linked page (take $\phi$ changing only one strategy), and for $\varepsilon = 0$
the two notions coincide; for $\varepsilon > 0$ the converse fails, since the per-pair errors of different recommendations add up under one
$\phi$. Bounds conditioned on each recommendation use a different normalization and are a separate statement.

## Expansion

This node states a precise result.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Canonical regret API: loss sequences and regret in repeated normal-form games (swap regret).

## Depends on

- [Gain from a switched recommendation](../correlated-equilibria/switch-gain.md)
- [Correlated equilibrium](../correlated-equilibria/is-correlated-eq.md)
- [Empirical distribution of play](empirical.md)

## Related topics

- [No conditional regret characterises correlated equilibria](../correlated-equilibria/is-correlated-eq-empirical-iff.md): the per-pair form, with conditional regrets and the correlated $\varepsilon$-equilibria of the linked page.

## Sources

- CS364A Lecture #18: From External Regret to Swap Regret and the Minimax Theorem — Tim Roughgarden, Stanford University (2013), Definition 1.2 and Proposition 1.3. <http://theory.stanford.edu/~tim/f13/l/l18.pdf>
- A Simple Adaptive Procedure Leading to Correlated Equilibrium — Hart and Mas-Colell, Econometrica 2000, Section 2 (correlated equilibrium inequalities). <http://ma.huji.ac.il/hart/papers/adapt0.pdf>
