# The multi-agent contract problem reduces to maximizing a set function

In a multi-agent contract instance, to induce effort exactly by the agents of $S$ at minimum cost the principal sets $\alpha_i = c_i / f(i \mid S \setminus \{i\})$ for $i \in S$, where $f(i \mid T) = f(T \cup \{i\}) - f(T)$, and $\alpha_i = 0$ otherwise (requiring all marginals positive). Hence the optimal principal utility equals

$$
\max_{S \subseteq [n]} g(S), \qquad g(S) = f(S)\Bigl(1 - \sum_{i \in S} \frac{c_i}{f(i \mid S \setminus \{i\})}\Bigr),
$$

when $f$ is submodular or more generally whenever these shares make $S$ an equilibrium.

## Proof sketch

Agent $i \in S$ is willing to work iff $\alpha_i f(i \mid S \setminus \{i\}) \ge c_i$, so the displayed share is the minimum. Agents outside $S$ receive nothing and therefore do not work. Substituting the minimal shares into $(1 - \sum_i \alpha_i) f(S)$ gives $g(S)$; any other contract inducing $S$ pays weakly more.

## Depends on

- [Multi-agent binary-action contract with a team reward function](multi-agent-binary-action-contract.md)

## Proof depends on

- [Multi-agent binary-action contract with a team reward function](multi-agent-binary-action-contract.md)

## Sources

- P. Dütting, T. Ezra, M. Feldman, T. Kesselheim, "Multi-Agent Contracts", STOC 2023, arXiv:2211.05434.
