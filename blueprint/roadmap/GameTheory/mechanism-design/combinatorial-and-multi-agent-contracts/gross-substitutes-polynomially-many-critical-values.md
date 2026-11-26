# Gross-substitutes success functions have polynomially many critical values

In a combinatorial contract instance whose success function $f$ is gross substitutes, the number of critical values of $\alpha \in [0, 1]$ is at most $\binom{n + 1}{2} = n(n+1)/2$, and they can be enumerated using polynomially many value queries to $f$.

## Proof sketch

The agent's demand at $\alpha$ maximizes $\alpha f(S) - c(S)$, equivalently $f(S) - c(S)/\alpha$, a demand query at prices $c/\alpha$ that rise uniformly as $\alpha$ decreases. Gross substitutes demands can be traced by a greedy algorithm, and along a uniform price increase each action enters the demanded set at most once and exits at most once relative to others; a potential argument on the sequence of greedy orders bounds the number of changes by $n(n+1)/2$.

## Depends on

- [Gross-substitutes success-probability function](gross-substitutes-success-probability.md)

## Proof depends on

- [Monotonicity of best responses along linear contracts](../hidden-action-principal-agent-contracts/linear-contract-best-response-monotonicity.md)

## Sources

- P. Dütting, T. Ezra, M. Feldman, T. Kesselheim, "Combinatorial Contracts", FOCS 2021, arXiv:2109.14260.
