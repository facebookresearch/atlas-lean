# Optimal isolation in the Erlang SIR model is bang-bang with at most two switches

Consider the [optimal isolation problem for the SIR model with Erlang infectious period](erlang-sir-isolation-control-problem.md): state $x = (S, Y_1, \dots, Y_n)$, control $u(t) \in [0, u_{\max}]$, cost $J = \int_0^T (A u + \beta S Y_n)\, dt$ with $A \ge 0$, free terminal time $T$ at which $Y_n(T) = \varepsilon$.

**Theorem.** For every $n \ge 1$ the optimal control $u^*$ is bang-bang. If $u^* \not\equiv 0$, there are $\tau_1, \tau_2 \in [0, T]$ with $\tau_1 \le \tau_2$ such that

$$u^*(t) = \begin{cases} 0, & t \in [0, \tau_1), \\ u_{\max}, & t \in [\tau_1, \tau_2], \\ 0, & t \in (\tau_2, T]. \end{cases}$$

Hence, apart from "do nothing", the admissible profiles are: constant maximal isolation ($\tau_1 = 0$, $\tau_2 = T$); delayed isolation ($\tau_1 > 0$, $\tau_2 = T$); reactive isolation ($\tau_1 = 0$, $\tau_2 < T$); and an isolation window with two switches in $(0, T)$, always from $0$ to $u_{\max}$ and back.

**Corollary.** If $A = 0$, that is, only the epidemic size is minimized, then $u^* \equiv u_{\max}$ on $[0, T]$.

## Depends on

- [Optimal isolation problem for the SIR model with Erlang infectious period](erlang-sir-isolation-control-problem.md)

## Expansion

With Hamiltonian $H = A u + \beta S Y_n + \lambda^T (f(x) + u g(x))$, the adjoint system $\dot\lambda = -\partial H / \partial x$, transversality $\lambda_S(T) = \lambda_{Y_k}(T) = 0$ for $k < n$ ($\lambda_{Y_n}(T)$ free) and $H \equiv 0$ (free final time), the control minimizes $H$ pointwise and is governed by the switching function

$$\psi = A - \sum_{k=1}^n \lambda_{Y_k} Y_k, \qquad \dot\psi = \beta S Y_n (1 - \lambda_S).$$

A singular arc would force $\psi = \dot\psi = \ddot\psi = 0$ on an interval, giving $\lambda_S = 1$ and, by the adjoint equations, $\lambda_{Y_k} = 0$ for all $k$; this contradicts $\psi = 0$ when $A > 0$ and the transversality $\lambda_S(T) = 0$ when $A = 0$. Next, $H(T) = 0$ and $\dot Y_n(T) < 0$ give $\lambda_{Y_n}(T) > 0$, and a backward-in-time argument shows $\lambda_{Y_k} \ge 0$ on $[0, T]$ and $\dot\lambda_S < 0$ throughout. A switch from $u_{\max}$ to $0$ followed by a switch back would need two zeros of $\dot\psi$, hence two times with $\lambda_S = 1$, impossible for strictly decreasing $\lambda_S$. This excludes three or more switches and fixes the order of two.

## Sources

- L. Bolzoni, R. Della Marca and M. Groppi, On the optimal control of SIR model with Erlang-distributed infectious period: isolation strategies, *J. Math. Biol.* 83 (2021), article 36, <https://doi.org/10.1007/s00285-021-01668-1>, PMCID PMC8456197. Theorem 2 (equation (13)) and Corollary 3.
