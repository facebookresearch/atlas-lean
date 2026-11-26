# Approximation ratio for the Nash social welfare objective

Throughout, $N = \{1, \dots, n\}$ is a finite set of agents and $M$ a finite set of indivisible goods; agent $i$ has an additive valuation $v_i(S) = \sum_{g \in S} v_i(g)$ with $v_i(g) \ge 0$. The Nash social welfare of an allocation is the geometric mean $\mathrm{NSW}(X) = \bigl(\prod_{i=1}^n v_i(X_i)\bigr)^{1/n}$. For $\rho \ge 1$, an algorithm is a $\rho$-approximation for maximum Nash social welfare if on every instance it outputs an allocation $X$ with $\rho \cdot \mathrm{NSW}(X) \ge \max_{Y} \mathrm{NSW}(Y)$, the maximum taken over all complete allocations $Y$. For non-additive monotone valuations $v_i : 2^M \to \mathbb{R}_{\ge 0}$ the same definition applies, with access to $v_i$ through value queries $S \mapsto v_i(S)$.

## Depends on

- [Nash Welfare](../../../not-yet-classified/part-01/indivisible/nash-welfare.md)

## Sources

- R. Cole, V. Gkatzelis, "Approximating the Nash Social Welfare with Indivisible Items", STOC 2015; SIAM Journal on Computing 47(3) (2018).
- E. Lee, "APX-hardness of maximizing Nash social welfare with indivisible items", Information Processing Letters 122 (2017).
