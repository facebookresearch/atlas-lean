# Present bias produces a preference reversal that exponential discounting excludes

Let $U_t = u(c_t) + \beta\sum_{s > t}\delta^{s-t}u(c_s)$ with $u(c) = c$. Take $\beta = 1/2$, $\delta = 1$ and two options: $A$ pays $1$ at date $1$, and $B$ pays $1.5$ at date $2$. At date $0$, $U_0(A) = 0.5 < 0.75 = U_0(B)$, so $B$ is preferred; at date $1$, $U_1(A) = 1 > 0.75 = U_1(B)$, so the ranking reverses. With exponential discounting ($\beta = 1$, any $\delta > 0$), for options paying at dates $t \ge 1$ one has $U_0 = \delta U_1$, so the ranking at date $0$ and at date $1$ always agree.

## Expansion

- A primary source that states this result in the form given here is to be located and checked before the statement is relied on.
