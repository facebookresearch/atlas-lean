# Game with incomplete information, dominant-strategy and ex-post Nash equilibria

A *game with strict incomplete information* has players $i$ with type spaces $T_i$, action spaces $X_i$, and private-value utilities $u_i(t_i, x)$. A strategy profile $s$ with $s_i : T_i \to X_i$ is a *dominant-strategy equilibrium* if for all $i$, $t_i$ and every action profile $x_{-i}$, $s_i(t_i)$ maximizes $u_i(t_i, \cdot, x_{-i})$; it is an *ex-post Nash equilibrium* if for every type profile $t$, the action profile $(s_j(t_j))_j$ is a pure Nash equilibrium of the complete-information game at $t$. An *indirect mechanism* maps action profiles to outcomes and payments.

## Depends on

- [Bayesian game](../../noncooperative-games/finite-bayesian-games-and-the-agent-normal-form/bayesian-game.md)
- [Pure Nash equilibrium of a finite game](../../noncooperative-games/potential-games/is-pure-nash-2.md)
- [Dominant-strategy profile](../revelation-principle/is-dominant-strategy-profile.md)

## Sources

- Noam Nisan, "Introduction to Mechanism Design (for Computer Scientists)", Algorithmic Game Theory, Cambridge University Press, 2007.
