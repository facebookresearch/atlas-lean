# Nash's theorem

Every finite game, with finitely many players, each having a finite nonempty set of pure
strategies, has a mixed Nash equilibrium.

Nash's proofs use Kakutani's fixed-point theorem (1950) and Brouwer's (1951). The proof below follows
the 1951 argument, with Brouwer's theorem for products of simplices.

## Proof

- Nash's map $\sigma_i'(t) = (\sigma_i(t) + g_i(t)) / (1 + \sum_{t'} g_i(t'))$, with gains $g_i(t) = \max(0, v_i(t, \sigma) - u_i(\sigma))$, where $u_i(\sigma)$ is the [expected payoff](expected-payoff.md) and $v_i(t, \sigma)$ that of the pure strategy $t$ against the others, is a continuous self-map of the product of the mixed-strategy simplices, so it has a fixed point.
- At a fixed point, some pure strategy $t$ in the support of $\sigma_i$ does no better than $\sigma_i$ (expected payoff is the $\sigma_i$-average of the pure payoffs), so $g_i(t) = 0$ and the fixed-point equation at $t$ forces $\sum_{t'} g_i(t') = 0$: no pure strategy gains, hence, by linearity, no mixed one, and $\sigma$ is a [mixed Nash equilibrium](is-mixed-nash.md).

## Background

- [Saddle point of a matrix game](../von-neumann-s-minimax-theorem/matrix-game-exists-is-saddle-point-on.md):
  background, the two-player zero-sum case, proved from Sion's minimax theorem.
- [Finite potential games have pure Nash equilibria](../potential-games/exists-is-pure-nash.md):
  background, a class of games with pure equilibria and an elementary proof.
- [A nondegenerate bimatrix game has an odd number of Nash equilibria](../bimatrix-games-and-the-lemke-howson-algorithm/odd-ncard-is-bimatrix-nash.md):
  background, a combinatorial existence proof for two players (Lemke–Howson).

## Informally uses

- [Brouwer's fixed-point theorem for products of simplices](../../../Topology/algebraic-topology/brouwer-fixed-point-theorem/exists-fixed-point-pi.md): applied to Nash's map.

## Sources

- J. Nash, "Equilibrium points in n-person games", Proc. Natl. Acad. Sci. USA 36 (1950), 48–49.
- J. Nash, "Non-cooperative games", Ann. of Math. 54 (1951), 286–295, Theorem 1.
