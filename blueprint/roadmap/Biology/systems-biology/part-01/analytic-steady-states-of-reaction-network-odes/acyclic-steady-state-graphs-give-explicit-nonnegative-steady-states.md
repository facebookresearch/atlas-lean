# Acyclic steady-state graphs give explicit nonnegative steady states

**Setting.** Consider an ODE model $\dot x = S\,F(x, p)$ with states $x \in \mathbb R^N_{\ge 0}$, stoichiometry matrix $S \in \mathbb Z^{N \times R}$ and flux vector $F$, where each flux is $F_l = k_l\,G_l(x, q)$ with a flux parameter $k_l > 0$, additional parameters $q$ and $G_l \ge 0$. Assume every out-flux of a state $x_i$ is at least linear in $x_i$, so the steady-state equation of $x_i$ can be written

$$0 = \sum \mathrm{in}_i - x_i \sum \mathrm{out}_i, \qquad\text{that is}\qquad x_i = \frac{\sum \mathrm{in}_i}{\sum \mathrm{out}_i}, \tag{$*$}$$

with nonnegative functions $\mathrm{in}_i, \mathrm{out}_i$ of the states and parameters and $\sum\mathrm{out}_i > 0$.

- A **head** of $x_i$ is a state that occurs on the right-hand side of $(*)$; $h(x_i)$ is the set of heads ($x_i$ itself may belong to it, when $(*)$ is nonlinear in $x_i$).
- The **steady-state graph** has the states as nodes and an edge $x_j \to x_i$ whenever $x_j \in h(x_i)$; a self-loop marks an equation nonlinear in $x_i$. The graph is **tree-like** if it has no directed cycles, self-loops included.

**Proposition 1.** If nonnegative steady-state values of all heads of $x_i$ are known, $(*)$ gives a nonnegative steady-state value of $x_i$; in particular this holds when $h(x_i) = \emptyset$.

**Proposition 2.** If the steady-state graph is tree-like, explicit nonnegative steady-state expressions are obtained for all states.

**Cycle splitting.** If a conserved quantity of the dynamics (there are $N - \mathrm{rank}\,S$ of them when all come from the stoichiometry) contains a state of a cycle, that state can be taken as a free parameter: its equation is dropped and its edges removed. Otherwise a cycle can be split by solving the equation of a cycle state $x_i$ for a flux parameter,

$$k_l = -\frac{1}{S_{il}\,G_l(x,q)}\sum_{j \neq l} S_{ij}\,k_j\,G_j(x,q).$$

**Proposition 3.** The number of steady-state equations in which $k_l$ appears equals the number of nonzero entries of column $l$ of $S$, so flux parameters with a single appearance split a cycle without creating new edges. With $\mu_i, \nu_i$ the numbers of in- and out-fluxes of $x_i$ and $\dim(x_i) = \min(\mu_i, \nu_i)$, solving for the unique in- or out-flux parameter when $\dim(x_i) = 1$ gives a nonnegative expression.

## Expansion

A finite acyclic digraph has a node without incoming edges, a state with no heads; Proposition 1 fixes it, and deleting it leaves an acyclic graph, so back-substitution in a topological order fixes all $N$ states with nonnegative values because sums, products and quotients of nonnegative quantities stay nonnegative. Nonlinear equations or feedback create cycles, which is exactly where polynomial equations of higher degree arise; each conserved quantity removes one equation and frees one variable, and solving for a flux parameter turns the corresponding equation into a linear one, at the price of substituting $k_l$ wherever else it appears (Proposition 3 counts those places from the stoichiometry). The sign of the expression for $k_l$ is guaranteed when $k_l$ is the only flux of its sign in the equation of $x_i$.

## Sources

- M. Rosenblatt, J. Timmer, D. Kaschek, "Customized steady-state constraints for parameter estimation in non-linear ordinary differential equation models", Frontiers in Cell and Developmental Biology (2016), Section 2 (Eqs. (4)–(7), Definitions 1–6, Propositions 1–3 with the proof of Proposition 2), <https://doi.org/10.3389/fcell.2016.00041>, PMCID PMC4863410.
