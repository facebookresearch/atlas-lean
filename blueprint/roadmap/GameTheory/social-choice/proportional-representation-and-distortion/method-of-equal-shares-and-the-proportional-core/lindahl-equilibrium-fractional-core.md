# Lindahl equilibrium yields a fractional core for public goods allocation

In a fractional public goods setting with $n$ agents, a set $P$ of projects with costs, a budget $L$, and continuous, concave, nondecreasing utilities $u_i(x)$ of the funding vector $x \in [0, 1]^P$ with $\sum_p \mathrm{cost}(p) x_p \le L$, a Lindahl equilibrium exists: personalized prices $q_{ip} \ge 0$ with $\sum_i q_{ip} \le \mathrm{cost}(p)$ for every project, with equality when $x_p > 0$, such that $x$ maximizes each agent's utility among funding vectors she can pay for with $L/n$ at her prices. Its allocation lies in the core with endowments: no coalition $S$ can use the budget $\lvert S \rvert L/n$ to fund a vector that every member of $S$ strictly prefers. For indivisible projects with additive utilities, normalized so that each agent's largest utility for a single project is $1$ (each agent is assumed to value some project positively), Fain, Munagala and Shah use a core with scaled utilities instead of endowments: for $\delta, \alpha \ge 0$ an outcome $c$ is a $(\delta, \alpha)$-core outcome if there is no coalition $S \subseteq N$ and feasible outcome $c'$ with $\frac{\lvert S \rvert}{n} u_i(c') \ge (1 + \delta) u_i(c) + \alpha$ for all $i \in S$, at least one inequality strict. A $(0, 0)$-core outcome need not exist. When the feasible outcomes are the bases of a matroid, a $(0, 2)$-core outcome exists, and for every $\varepsilon > 0$ a $(0, 2 + \varepsilon)$-core outcome can be computed in time polynomial in $n$, the number $m$ of projects and $1/\varepsilon$. For $K$ packing constraints $Ax \le b$, a budget being one such constraint, of width $\rho = \max_k \sum_j a_{kj}/b_k$ with $b_k = \omega(\log K/\delta^2)$ for every $k$ and a constant $\delta \in (0, 1)$, a $(\delta, \alpha)$-core outcome with $\alpha = O\bigl(\delta^{-4} \log(\min(V_{\max}, n, \rho) \cdot \log^* V_{\max}/\delta)\bigr)$ can be computed in polynomial time, where $V_{\max}$ is the largest utility of an agent for a feasible outcome.

## Proof sketch

Existence follows from a fixed-point argument. For the core property, if a coalition $S$ could fund $y$ preferred by all members, then each member's personalized cost of $y$ would exceed $L/n$, since otherwise she would have chosen $y$; summing over $S$ and using $\sum_i q_{ip} \le \mathrm{cost}(p)$ shows that $y$ costs more than $\lvert S\rvert L/n$, a contradiction. For matroid constraints the guarantees come from local optima of a smoothed Nash welfare objective that adds a constant to each agent's utility, an approximate local optimum found by local search giving the additive $2 + \varepsilon$ in polynomial time; for packing constraints an approximate fractional core solution is rounded.

## Depends on

- [Participatory budgeting with approval ballots and project costs](participatory-budgeting-approval-costs.md)
- [Core of an approval-based committee election](core-of-approval-committee-election.md)

## Sources

- D. K. Foley, "Lindahl's Solution and the Core of an Economy with Public Goods", Econometrica 38(1) (1970).
- B. Fain, K. Munagala, N. Shah, "Fair Allocation of Indivisible Public Goods", EC 2018, arXiv:1805.03164.
