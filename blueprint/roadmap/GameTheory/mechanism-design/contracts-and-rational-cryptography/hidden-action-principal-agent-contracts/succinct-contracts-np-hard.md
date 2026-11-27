# Optimal contracts are hard to compute with succinct outcome spaces

Consider principal-agent instances whose outcome space is $\{0, 1\}^d$, where each action $i$ induces a product distribution in which coordinate $\ell$ equals $1$ independently with probability $q_{i,\ell}$, and the reward is additive across coordinates. Computing an optimal contract is NP-hard in this model already for every constant number $n \ge 3$ of actions, and with an arbitrary number of actions it is NP-hard to approximate the optimal principal utility within any constant factor $c \ge 1$ (also by $\delta$-incentive-compatible contracts when $\delta$ is small enough in terms of $c$). By contrast, the optimal linear contract is computable in polynomial time, and for every constant $\delta > 0$ some polynomial-time computable $\delta$-incentive-compatible linear contract is a constant-factor approximation of the optimal welfare.

## Proof sketch

Reduce from gap MAX-3SAT: it is NP-hard to tell satisfiable formulas from those in which no assignment satisfies more than a $7/8 + \alpha$ fraction of the clauses. Satisfiable formulas map to instances in which an incentive-compatible contract extracts the full welfare (no gap between first and second best), and far-from-satisfiable ones to instances with a constant-factor gap between the two. With product distributions, the min-pay programs have exponentially many variables, which is where the hardness lives. Linear contracts only need expected rewards, which are computable coordinatewise.

## Depends on

- [Hidden-action principal-agent instance and contract](hidden-action-principal-agent-instance.md)
- [Linear contract and its critical values](linear-contract-critical-values.md)

## Proof depends on

- [Optimal contracts via one linear program per action](optimal-contract-min-pay-linear-programs.md)

## Sources

- P. Dütting, T. Roughgarden, I. Talgam-Cohen, "The Complexity of Contracts", SODA 2020; SIAM Journal on Computing 50(1) (2021), arXiv:2002.12034, Theorems 1.2 and 1.4, Proposition B.1 and Proposition A.3.
