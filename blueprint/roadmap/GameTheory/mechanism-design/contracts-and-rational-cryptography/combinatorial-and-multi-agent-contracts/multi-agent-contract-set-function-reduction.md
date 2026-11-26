# The multi-agent contract problem reduces to maximizing a set function

In a multi-agent contract instance, write $f(i \mid T) = f(T \cup \{i\}) - f(T)$. A set $S$ of agents can be induced in equilibrium by some linear contract $\alpha \in \mathbb{R}_{\ge 0}^n$ if and only if no agent $i \in S$ has both $f(i \mid S \setminus \{i\}) = 0$ and $c_i > 0$. For such $S$, the contract that induces $S$ and maximizes the principal's utility sets

$$
\alpha_i = \frac{c_i}{f(i \mid S \setminus \{i\})} \quad \text{for } i \in S \text{ with } f(i \mid S \setminus \{i\}) > 0, \qquad \alpha_i = 0 \quad \text{otherwise}.
$$

Hence the optimal principal utility equals

$$
\max_{S \subseteq [n]} g(S), \qquad g(S) = f(S)\Bigl(1 - \sum_{i \in S} \frac{c_i}{f(i \mid S \setminus \{i\})}\Bigr),
$$

with the conventions $c_i/f(i \mid S \setminus \{i\}) = 0$ when $c_i = 0 = f(i \mid S \setminus \{i\})$, and $= +\infty$ when $c_i > 0 = f(i \mid S \setminus \{i\})$, so that sets that cannot be induced have $g(S) = -\infty$ and are excluded from the maximum. This holds for every monotone $f$; among all limited-liability contracts paying $t_i(1), t_i(0) \ge 0$ on success and failure, the displayed linear contract, which pays $t_i(1) = \alpha_i r(1) = \alpha_i$ and $t_i(0) = 0$ under the normalization $r(1) = 1$, $r(0) = 0$ with success probability $f(S) \in [0, 1]$, is optimal for $S$.

## Proof sketch

For linear $\alpha$, agent $i \in S$ is willing to work iff $\alpha_i f(i \mid S \setminus \{i\}) \ge c_i$, which no $\alpha_i \ge 0$ satisfies when the marginal is $0$ and $c_i > 0$, and which holds with $\alpha_i = 0$ when $c_i = 0$; otherwise the displayed share is the minimum. With $\alpha_i = 0$, an agent outside $S$ gains $-c_i \le 0$ by working, so it does not deviate. The principal's utility $(1 - \sum_i \alpha_i) f(S)$ is decreasing in every share, so the minimal shares are optimal and give $g(S)$. For a general contract with payments $t_i(1), t_i(0)$, agent $i$'s expected payment is $t_i(0) + f(S)(t_i(1) - t_i(0))$ because $f(S)$ is a success probability, so the incentive constraint of $i \in S$ reads $(t_i(1) - t_i(0))\,f(i \mid S \setminus \{i\}) \ge c_i$. The principal's utility $f(S) - \sum_i \bigl(f(S)\,t_i(1) + (1 - f(S))\,t_i(0)\bigr)$ is nonincreasing in both payments, so $t_i(0) = 0$ and the minimal feasible $t_i(1)$ are optimal; since $r(1) = 1$, this cash payment on success equals the displayed share $\alpha_i$.

## Depends on

- [Multi-agent binary-action contract with a team reward function](multi-agent-binary-action-contract.md)
- [Submodular set function](../../../../ComputerScience/approximation-algorithms/maximum-n-times-coverage/is-submodular.md)

## Sources

- P. Dütting, T. Ezra, M. Feldman, T. Kesselheim, "Multi-Agent Contracts", STOC 2023, arXiv:2211.05434, Section 2 (Proposition 2.1 and the reduction following it).
