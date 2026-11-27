# Monotonicity of best responses along linear contracts

Assume, as Dütting, Roughgarden and Talgam-Cohen do, that distinct actions have distinct expected rewards and that an action with larger expected reward also has larger cost. Under linear contracts, as $\alpha$ increases through the critical values, the agent's best-response action (with tie-breaking in favour of the principal) changes to actions of strictly larger expected reward $R_i$, strictly larger cost $c_i$ and weakly larger welfare $R_i - c_i$. An optimal linear contract is attained at $\alpha = 0$ or at one of the critical values, so the best linear contract is found by evaluating the principal's utility at these finitely many points, which depend only on the pairs $(R_i, c_i)$.

## Proof sketch

The agent's utility $\alpha R_i - c_i$ is affine in $\alpha$ with slope $R_i$; the upper envelope of affine functions is convex and piecewise affine, and its slopes increase with $\alpha$, giving monotone expected rewards; among actions on the envelope, larger slope at a later breakpoint forces larger cost. Between consecutive breakpoints the principal's utility $(1 - \alpha) R_i$ decreases in $\alpha$, so on each piece it is maximized at the left endpoint, which is $0$ or a critical value.

## Depends on

- [Linear contract and its critical values](linear-contract-critical-values.md)

## Sources

- P. Dütting, T. Roughgarden, I. Talgam-Cohen, "Simple versus Optimal Contracts", EC 2019, arXiv:1808.03713.
