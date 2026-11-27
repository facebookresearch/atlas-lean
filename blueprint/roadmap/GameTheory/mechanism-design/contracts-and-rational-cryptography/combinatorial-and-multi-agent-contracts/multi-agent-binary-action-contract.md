# Multi-agent binary-action contract with a team reward function

A multi-agent contract instance has a set $[n]$ of agents, each choosing to exert effort (cost $c_i \ge 0$) or not (cost $0$), and a binary outcome, success or failure, with the principal's reward normalized to $r(1) = 1$ on success and $r(0) = 0$ on failure. A monotone success probability function $f : 2^{[n]} \to [0, 1]$ with $f(\emptyset) = 0$ gives the probability of success when exactly the agents in $S$ exert effort; by the normalization, $f(S)$ is also the principal's expected reward, so $f$ is called the reward function. The principal offers linear contracts $\alpha \in \mathbb{R}_{\ge 0}^n$, paying agent $i$ the share $\alpha_i$ of the reward, that is, $\alpha_i$ on success and $0$ on failure (nonnegative payments, i.e. limited liability; shares need not sum to at most $1$, and the principal's utility may then be negative). A set $S$ is induced in equilibrium by $\alpha$ if for every $i \in S$, $\alpha_i f(S) - c_i \ge \alpha_i f(S \setminus \{i\})$, and for every $i \notin S$, $\alpha_i f(S \cup \{i\}) - c_i \le \alpha_i f(S)$. The principal's utility is $\bigl(1 - \sum_i \alpha_i\bigr) f(S)$.

## Depends on

- [Combinatorial-actions contract with a binary outcome](combinatorial-actions-binary-outcome-contract.md)
- [Combinatorial agency and the price of unaccountability](../combinatorial-agency-and-the-price-of-unaccountability.md)
- [Submodular set function](../../../../ComputerScience/approximation-algorithms/maximum-n-times-coverage/is-submodular.md)

## Sources

- P. Dütting, T. Ezra, M. Feldman, T. Kesselheim, "Multi-Agent Contracts", STOC 2023, arXiv:2211.05434.
- M. Babaioff, M. Feldman, N. Nisan, "Combinatorial Agency", EC 2006; Journal of Economic Theory 147(3) (2012).
