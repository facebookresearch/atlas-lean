# Greedy stationary control policies for undesirable stationary mass

**Setting.** The state space $\{0,1\}^n$ of a gene network chain with transition matrix $P$ is split into desirable states $D$ and undesirable states $U$ (e.g. by the value of a target gene). A **stationary control policy** for a control gene $g$ is a map $u_g : \{0,1\}^n \to \{0,1\}$; $u_g(x) = 1$ means that in state $x$ the value of $g$ is flipped before the next transition, which replaces row $p_x$ by $p_{\tilde x}$ ($\tilde x$ = $x$ with $g$ flipped). The objective is to minimize the undesirable stationary mass $\pi_U = \sum_{x\in U}\pi_x$ of the controlled chain.

**Policies.**
- *Mean first passage time (MFPT):* with $K_U$ (from $D$ to $U$) and $K_D$ (from $U$ to $D$) the mean first passage times, flip in a desirable $x$ if $K_U(\tilde x) - K_U(x) \ge \lambda$ and in an undesirable $x$ if $K_D(x) - K_D(\tilde x) \ge \lambda$.
- *Steady-state distribution (SSD):* for each pair $(x,\tilde x)$, compute the undesirable mass $\tilde\pi_U(x)$, $\tilde\pi_U(\tilde x)$ after the corresponding one-row perturbation, and control toward the smaller one when it is below $\pi_U$; combine all such decisions.
- *Conservative SSD (CSSD):* starting from $P_0 = P$, at iteration $k$ choose among undecided states the one-row perturbation of $P_{k-1}$ with the largest decrease of undesirable mass, apply it only if the mass decreases, and update $\pi$ and $Z$ exactly; stop when no perturbation decreases the mass.

**Theorem.** If CSSD performs $K$ iterations producing $P_0, P_1, \dots, P_K$, then

$$\pi_U(P_K) \le \pi_U(P_{K-1}) \le \cdots \le \pi_U(P_0) = \pi_U,$$

so the derived policy never increases the undesirable stationary mass. MFPT and SSD carry no such guarantee, because their independently chosen one-row changes interact.

## Depends on

- [Stationary distribution of a rank-one perturbed gene network chain](stationary-distribution-of-a-rank-one-perturbed-gene-network-chain.md)

## Expansion

Each CSSD step is a single-row (rank-one) perturbation of the current matrix, so the exact new stationary distribution and fundamental matrix follow from the rank-one update formulas, and the step is accepted only when the exact undesirable mass decreases; induction on $k$ gives monotonicity. The SSD and MFPT policies cost $O(2^n)$ decisions with one analytic evaluation each, while CSSD trades extra iterations for the guarantee; all avoid the $O(2^{2^n})$ search over policies and the cost-function tuning of discounted dynamic programming.

## Sources

- X. Qian, I. Ivanov, N. Ghaffari, E. R. Dougherty, "Intervention in gene regulatory networks via greedy control policies based on long-run behavior", BMC Systems Biology 3 (2009) 61, MFPT, BOA, SSD and CSSD control policies and Theorem 4, <https://doi.org/10.1186/1752-0509-3-61>, PMCID PMC2728102.
