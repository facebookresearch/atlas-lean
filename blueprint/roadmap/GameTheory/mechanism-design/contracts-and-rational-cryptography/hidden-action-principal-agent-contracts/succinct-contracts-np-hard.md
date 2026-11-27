# Optimal contracts are hard to compute with succinct outcome spaces

Consider principal-agent instances whose outcome space is $\{0, 1\}^d$, where each action $i$ induces a product distribution in which coordinate $\ell$ equals $1$ independently with probability $q_{i,\ell}$, and the reward is additive across coordinates. As in Dütting, Roughgarden and Talgam-Cohen (Section 2), the instance is normalized, $R_i \le 1$ for every action; every action has nonnegative expected welfare $R_i - c_i \ge 0$, a separate assumption that together with normalization gives $c_i \le 1$ (normalization alone does not: an action may have reward $1$ and cost $2$); action $1$ has zero cost; and the input is the vector of costs, the vector of item rewards and the matrix of probabilities $q_{i,\ell}$, all given in binary with a number of bits of precision polynomial in $n$ and $d$. Since an additive slack is meaningful only on this fixed scale, for $\delta \ge 0$ an action $i$ is called $\delta$-incentive-compatible ($\delta$-IC) under a contract if $T_i - c_i \ge T_k - c_k - \delta$ for every action $k$, where $T_i$ is the expected payment of action $i$; the agent then chooses, among the $\delta$-IC actions, one best for the principal. Computing an optimal contract is NP-hard in this model already for every constant number $n \ge 3$ of actions, and so is the $\delta$-IC version when $\delta$ is part of the input (Proposition B.1). The $\delta$-IC hardness does not hold for every fixed slack: when $\delta \ge 1$, since all costs lie in $[0, 1]$, the zero contract makes every action $\delta$-IC, so the principal obtains $\max_i R_i$, an upper bound for every contract because payments are nonnegative, and this value is computable coordinatewise. With an arbitrary number of actions it is NP-hard to approximate the optimal principal utility within any constant factor $c \ge 1$; for every constant $c \ge 5$ and $\delta \le (1/(4c))^c$ it is even NP-hard to find a $\delta$-IC contract guaranteeing the principal more than $\frac{2}{c}\mathrm{OPT}$, where $\mathrm{OPT}$ is the optimal utility of an IC contract. By contrast, the optimal linear contract is computable in polynomial time, and for every constant $\delta > 0$ some polynomial-time computable $\delta$-incentive-compatible linear contract is a constant-factor approximation of the optimal welfare.

## Proof sketch

Reduce from gap MAX-3SAT: it is NP-hard to tell satisfiable formulas from those in which no assignment satisfies more than a $7/8 + \alpha$ fraction of the clauses. Satisfiable formulas map to instances in which an incentive-compatible contract extracts the full welfare (no gap between first and second best), and far-from-satisfiable ones to instances with a constant-factor gap between the two. With product distributions, the min-pay programs have exponentially many variables, which is where the hardness lives. Linear contracts only need expected rewards, which are computable coordinatewise.

## Depends on

- [Hidden-action principal-agent instance and contract](hidden-action-principal-agent-instance.md)
- [Linear contract and its critical values](linear-contract-critical-values.md)

## Proof depends on

- [Optimal contracts via one linear program per action](optimal-contract-min-pay-linear-programs.md)

## Sources

- P. Dütting, T. Roughgarden, I. Talgam-Cohen, "The Complexity of Contracts", SODA 2020; SIAM Journal on Computing 50(1) (2021), arXiv:2002.12034, Definition 2.1, Theorems 1.2 to 1.4, Proposition B.1 and Proposition A.3.
