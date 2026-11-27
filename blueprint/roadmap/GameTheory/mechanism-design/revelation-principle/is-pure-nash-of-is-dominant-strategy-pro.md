# Dominant strategies give pure Nash equilibria

Let $I$ be a set of agents; agent $i$ has a set $\Theta_i$ of types and a set $X_i$ of actions, and $O$ is a set of outcomes. A mechanism is a map $g : \prod_i X_i \to O$; a direct mechanism is a map $f : \prod_i \Theta_i \to O$. For a profile $x$ and $a \in X_i$, $(a, x_{-i})$ is $x$ with its $i$-th entry replaced by $a$.
Let $u_i(\theta_i, o)$ be private-value utilities. If $s$ is a profile of dominant strategies in the
mechanism $g$, then at every type profile $\theta$ the action profile $(s_j(\theta_j))_{j \in I}$ is a pure
Nash equilibrium of the complete-information game in which player $i$ chooses $x_i \in X_i$ and incurs the
cost $-u_i(\theta_i, g(x))$: no player lowers its cost by a unilateral deviation.

## Background

- [Dominant-strategy profile](is-dominant-strategy-profile.md): the hypothesis, applied at the equilibrium profile itself.
- [Potential games](../../noncooperative-games/potential-games/README.md): where pure Nash equilibria of cost games are defined and shown to exist for exact potential games.
