# Potential functions certify competitiveness

Let $A$ be a deterministic online strategy and $\Phi$ a nonnegative function of the pair (online state, offline state). If for every request $r$ and every valid offline step from $s^{\mathrm{off}}$ to $s'^{\mathrm{off}}$, the online step from $s^{\mathrm{on}}$ to $s'^{\mathrm{on}}$ satisfies

$$
\mathrm{cost}_A + \Phi(s'^{\mathrm{on}}, s'^{\mathrm{off}}) \le c \cdot \mathrm{cost}_{\mathrm{off}} + \Phi(s^{\mathrm{on}}, s^{\mathrm{off}}),
$$

then for every request sequence and every offline schedule $S$ from the same start, $\mathrm{cost}_A \le c \cdot \mathrm{cost}(S) + \Phi(s_0, s_0)$; in particular $A$ is $(c, b)$-competitive with $b = \sup_{s_0} \Phi(s_0, s_0)$.

## Proof sketch

Sum the inequality along the joint run and telescope; the final potential is nonnegative.

## Depends on

- [Online request-serving problem and competitive ratio](online-problem-and-competitive-ratio.md)
- [Amortized cost of an operation](../../data-structures/amortized-analysis/amortized-cost.md)

## Proof depends on

- [Potential method: amortized costs bound actual costs](../../data-structures/amortized-analysis/sum-cost-le-sum-amortized-cost.md)

## Sources

- D. D. Sleator and R. E. Tarjan, "Amortized Efficiency of List Update and Paging Rules", Communications of the ACM 28(2), 1985.
- A. Borodin and R. El-Yaniv, "Online Computation and Competitive Analysis", Cambridge University Press, 1998.
