# Private provision of a public good and a correcting subsidy

Let $n \ge 2$ consumers have quasilinear utilities $x_i + v(G)$ in an unrestricted private numeraire $x_i$ (no wealth constraint binds), where $G = \sum_i g_i$ is the total of nonnegative contributions, each unit of the public good costs $c > 0$ of the private good, and $v$ is differentiable, strictly concave and increasing, with $v'(0) > c$ and $v'(G) \to 0$ as $G \to \infty$. (i) The surplus $n v(G) - cG$ is maximized at the unique $G^*$ with $n v'(G^*) = c$ (the Samuelson condition). (ii) In every Nash equilibrium of voluntary contributions the total $G^N$ satisfies $v'(G^N) = c$, so $G^N < G^*$. (iii) If each contributor's cost per unit is reduced to $c/n$ by a subsidy at rate $c(1 - 1/n)$ financed by lump-sum taxes that do not depend on any consumer's own contribution (set to balance the budget at the implemented total $G^*$), the equilibrium total satisfies $v'(G) = c/n$, which is the Samuelson condition, so the subsidy implements $G^*$.

Proof. (i) The derivative $n v' - c$ is strictly decreasing, positive at $0$ and eventually negative. (ii) A contributor's payoff in $g_i$ is $v(g_i + G_{-i}) - c g_i$ plus a constant, so a best response sets $v'(G) \le c$ with equality when $g_i > 0$; some $g_i > 0$ because $v'(0) > c$, so $v'(G^N) = c$, and $v'(G^N) = c > c/n = v'(G^*)$ with $v'$ strictly decreasing gives $G^N < G^*$. (iii) The same argument with unit cost $c/n$; a tax that does not depend on the consumer's own contribution does not change the marginal condition.

## Depends on

- [Total surplus from a public good](surplus.md): total surplus from a public good.

## Proof depends on

- [Samuelson condition at an interior optimum](sum-marginal-benefit-eq-marginal-cost.md): the Samuelson condition at an interior optimum.

## Sources

- The statement is derived on this page from its definitions and the linked results; no external source is followed.
