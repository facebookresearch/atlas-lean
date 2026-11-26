# Monotonicity of best responses along linear contracts

Under linear contracts, as $\alpha$ increases through the critical values, the agent's best-response action (with tie-breaking in favour of the principal) changes to actions of strictly larger expected reward $R_i$ and strictly larger cost $c_i$. An optimal linear contract is attained at one of the critical values, so the best linear contract can be found in time $O(n \log n)$ from the values $(R_i, c_i)$.

## Proof sketch

The agent's utility $\alpha R_i - c_i$ is affine in $\alpha$ with slope $R_i$; the upper envelope of affine functions is convex and piecewise affine, and its slopes increase with $\alpha$, giving monotone expected rewards; among actions on the envelope, larger slope at a later breakpoint forces larger cost. Between consecutive breakpoints the principal's utility $(1 - \alpha) R_i$ decreases in $\alpha$, so it is maximized at the left endpoint, a critical value. Computing the envelope is a convex-hull computation.

## Depends on

- [Linear contract and its critical values](linear-contract-critical-values.md)

## Proof depends on

- [Linear contract and its critical values](linear-contract-critical-values.md)

## Sources

- P. Dütting, T. Roughgarden, I. Talgam-Cohen, "Simple versus Optimal Contracts", EC 2019, arXiv:1808.03713.
