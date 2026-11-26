# Ideal square-law nMOS drain current

Let $\beta > 0$. For overdrive voltage $u$ and drain-source voltage $V$, let the drain current be

$$I(u, V) = \begin{cases} 0 & u \le 0,\\ \beta\,(uV - V^2/2) & u > 0,\ V \le u,\\ \beta u^2/2 & u > 0,\ V > u. \end{cases}$$

Write $I_{\mathrm{tri}}(u, V) = \beta(uV - V^2/2)$ and $I_{\mathrm{sat}}(u) = \beta u^2/2$. Then:

1. $I(u, V) = 0$ for $V \ge 0$, $u \le 0$; $I(u, V) = I_{\mathrm{tri}}(u, V)$ for $0 \le V \le u$, $u > 0$; $I(u, V) = I_{\mathrm{sat}}(u)$ for $0 < u \le V$.
2. $I_{\mathrm{tri}}(u, u) = I_{\mathrm{sat}}(u)$ for every $u$.
3. For $V \ge 0$, $u \mapsto I(u, V)$ is continuous at $u = 0$; for $u > 0$, $V \mapsto I(u, V)$ is continuous at $V = u$, and $I$ is jointly continuous at $(u, u)$.
4. For $u < 0$: $\partial_u I(u, V) = 0$ and $\partial_V I(u, V) = 0$.
5. For $0 < V < u$: $\partial_u I = \beta V$ and $\partial_V I = \beta(u - V)$.
6. For $0 < u < V$: $\partial_u I = \beta u$ and $\partial_V I = 0$.
7. $\beta(u - V) \ge 0$ whenever $V \le u$.
8. $I(u, V) \ge 0$ whenever $V \ge 0$.
