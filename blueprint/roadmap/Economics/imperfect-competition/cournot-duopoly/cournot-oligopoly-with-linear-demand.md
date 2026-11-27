# Cournot equilibrium with linear demand and n firms

Let inverse demand be $P(Q) = \max(a - bQ, 0)$ with $a, b > 0$, and let $n \ge 1$ firms have constant marginal costs $c_i$ with $0 < c_i < a$ and profits $q_i(P(Q) - c_i)$ on quantities $q_i \ge 0$, without capacity limits. If $a - (n+1)c_i + \sum_j c_j > 0$ for every $i$, then $q_i^\star = (a - (n+1)c_i + \sum_j c_j)/((n+1)b)$ is the unique Nash equilibrium. Proof sketch: in any equilibrium the price is positive, since otherwise every active firm makes a loss; on the region of positive price the game has the differentiable, strictly concave exact potential $aQ - \tfrac b2(Q^2 + \sum_i q_i^2) - \sum_i c_iq_i$, defined on the product $[0, \infty)^n$ of the strategy sets, whose unique maximizer over $q \ge 0$ is $q^\star$, and every best-response inequality holds there. Positive costs are needed: with $a = b = 1$, $n = 2$ and $c_1 = c_2 = 0$, the profile $(1, 1)$ gives price $0$ and every unilateral deviation still earns $0$, so it is a second equilibrium besides $(1/3, 1/3)$. Capacity limits and corner solutions are separate statements.

## Expansion

A sound expansion specifies the following prerequisites and links their statements.

- A differentiable concave exact potential on a Cartesian product of convex strategy sets: profiles at which no player can improve unilaterally are exactly the maximizers of the potential (for the quadratic potential here, equivalently the Karush–Kuhn–Tucker conditions).

## Sources

- The statement is derived on this page from its definitions and the linked results; no external source is followed.
