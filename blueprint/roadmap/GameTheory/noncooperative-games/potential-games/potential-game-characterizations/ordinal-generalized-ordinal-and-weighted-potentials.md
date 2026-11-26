# Ordinal, generalized ordinal and weighted potentials

Let $G$ be a cost-minimization game and $\Phi : \prod_i S_i \to \mathbb{R}$. For a unilateral deviation of player $i$ from $s$ to $(a, s_{-i})$:

- $\Phi$ is an *ordinal potential* if $c_i(a, s_{-i}) < c_i(s) \iff \Phi(a, s_{-i}) < \Phi(s)$;
- $\Phi$ is a *generalized ordinal potential* if $c_i(a, s_{-i}) < c_i(s)$ implies $\Phi(a, s_{-i}) < \Phi(s)$;
- for positive weights $w_i > 0$, $\Phi$ is a *$w$-potential* if $c_i(a, s_{-i}) - c_i(s) = w_i\,(\Phi(a, s_{-i}) - \Phi(s))$.

An exact potential is a $w$-potential with all $w_i = 1$.

## Depends on

- [Exact potential](../is-exact-potential.md)
- [Improving move](../improving-move.md)

## Sources

- Dov Monderer and Lloyd S. Shapley, "Potential Games", Games and Economic Behavior, 1996.
