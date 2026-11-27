# Optimal isolation problem for the SIR model with Erlang infectious period

Let $n \ge 1$ be an integer and let $\beta, \gamma > 0$. An infectious period with the Erlang law $\mathrm{Erlang}(n, n\gamma)$, of density

$$f(x; n, n\gamma) = \frac{(n\gamma)^n}{(n-1)!}\, x^{n-1} e^{-n\gamma x}, \qquad x \ge 0,$$

is the sum of $n$ independent exponential stages of mean $1/(n\gamma)$. By the method of stages, with an isolation rate $u(t) \in U = [0, u_{\max}]$ applied to infected units, the controlled SIR system is

$$\dot S = -\beta S I, \quad \dot I_1 = \beta S I - (n\gamma + u(t)) I_1, \quad \dot I_j = n\gamma I_{j-1} - (n\gamma + u(t)) I_j \ \ (j = 2, \dots, n),$$

with $I = \sum_{j=1}^n I_j$. Write $\mu = n\gamma$ and $Y_k = \sum_{j=1}^k I_j$, so $Y_n = I$. Then

$$\dot S = -\beta S Y_n, \quad \dot Y_1 = \beta S Y_n - (\mu + u) Y_1, \quad \dot Y_k = \beta S Y_n - u Y_k - \mu (Y_k - Y_{k-1}) \ \ (k = 2, \dots, n),$$

which has the control-affine form $\dot x = f(x) + u(t) g(x)$ with $x = (S, Y_1, \dots, Y_n)^T$ and $g(x) = (0, -Y_1, \dots, -Y_n)^T$. Because the $Y_k$ are cumulative sums of the nonnegative stage variables $I_j = Y_j - Y_{j-1}$ ($Y_0 = 0$), the physical states satisfy $0 \le Y_1 \le \cdots \le Y_n$. For $n = 1$ and $u \equiv 0$ the system is the [Kermack–McKendrick SIR system](../../../kermack-mckendrick-sir-model/is-solution.md) with $N = 1$.

Fix $0 < \varepsilon < 1$ and initial data $S(0) = S_0 > 0$ and $0 \le Y_1(0) \le \cdots \le Y_{n-1}(0) \le Y_n(0)$ with $Y_n(0) > \varepsilon$, that is, $I_j(0) \ge 0$ for every stage. The terminal time is the free extinction time

$$T = \inf\{ t \ge 0 : Y_n(t) = \varepsilon \}.$$

For every $u \in \Omega$ (defined below), the set

$$D = \{ x \in \mathbb{R}_+^{n+1} : 0 \le Y_1 \le \cdots \le Y_n,\ S \le S_0,\ S + Y_n \le S_0 + Y_n(0) \}$$

is positively invariant. For a relative cost $A \ge 0$ of isolation effort per unit time over the cost of one new infection, the optimal control problem is to minimize

$$J(u) = \int_0^T \big( A\, u(t) + \beta S(t) Y_n(t) \big)\, dt$$

over $\Omega = \{ u \in L^1(0, T) : u(t) \in [0, u_{\max}] \}$.

**Theorem (existence).** The problem admits an optimal control $u^*$.

## Expansion

In stage coordinates, $\dot I_j \ge -(\mu + u) I_j$ for each stage while $S$ and the other stages are nonnegative, so the stages stay nonnegative, which is the ordering $0 \le Y_1 \le \cdots \le Y_n$; $S$ is nonincreasing and stays positive; and $(S + Y_n)' = -u Y_n - \mu (Y_n - Y_{n-1}) \le 0$ on the ordered set (for $n = 1$, $(S + Y_1)' = -(\mu + u) Y_1$). Without the ordering this fails: with $n = 2$, $u = 0$ and $Y_1 > Y_2$ at $S = S_0$ on the face $S + Y_2 = S_0 + Y_2(0)$, $(S + Y_2)' = \mu (Y_1 - Y_2) > 0$. Existence follows from the corollary of Filippov's theorem: the control set $[0, u_{\max}]$ is compact; for each $x \in D$ the velocity set $\{ f(x) + u g(x) : u \in U \}$ is a segment, hence convex, because the dynamics are affine in $u$; and since states in $D$ and controls are bounded, $|f(x) + u g(x)| \le C(1 + |x|)$. The cumulative variables $Y_k$ turn the chain of stages into a system in which only $Y_n$ enters the incidence, which is what makes the adjoint analysis of the bang-bang theorem tractable.

## Sources

- L. Bolzoni, R. Della Marca and M. Groppi, On the optimal control of SIR model with Erlang-distributed infectious period: isolation strategies, *J. Math. Biol.* 83 (2021), article 36, <https://doi.org/10.1007/s00285-021-01668-1>, PMCID PMC8456197. Model equations (1)-(8), including the change to cumulative variables before (2), and Theorem 1.
