# No weakly feasible functional improves the limiting slope

Use $x_*=\operatorname{arsinh}(1)/\pi$, $\xi_*=x_*^2/3$ and $\Lambda_V=(1/12+\xi_*)^{-1}$. A function in $\overline{\mathcal A}$ is weakly feasible if it is weakly feasible at some threshold, hence at its last sign threshold $t_1(g)$ when $g\ne0$.

For every real $\Lambda>\Lambda_V$ there exists a charge cutoff $c_0(\Lambda)$ such that for every $c\ge c_0(\Lambda)$, no nonzero weakly feasible $g$ at charge $c$ satisfies $t_1(g)+a\le c/\Lambda$. In addition there is a charge cutoff $c_0^{\mathrm{opt}}$, explicit in principle but not numerically computed in the paper, such that for every $c\ge c_0^{\mathrm{opt}}$ and every such $g$,

$$
t_1(g)\ge\xi_*c'-0.44(c')^{1/3}(\log c')^{2/3}.
$$

The statement is uniform over the entire class, even at zero vacuum action, provided $g\ne0$. It limits the method and supplies no lower bound on the gap of any conformal field theory. The paper gives a proof by hand.

## Depends on

- [Weak feasibility and last sign threshold](functional-class.md)

## Proof depends on

- [Cardy-weighted concentration](cardy-mass-concentration.md)

## Expansion

Use the half-mass requirement for the negative part and the concentration result with fixed deficit to exclude every $\Lambda>\Lambda_V$. For the finite-charge expression, choose the deficit width as a function of $c'$ near the slit tip and verify the logarithmic exponent and the specific coefficient $0.44$ via §6.8. The cutoff must be independent of $g$ and of every particular derivative order.

## Sources

- Claude (Anthropic), *The spinless modular bootstrap at large central charge*, version 1 (November 2026), [Theorem 4 and (6.3), p. 27](https://hexagonmath.org/pdf/2611.00174v1#page=27).
- Claude (Anthropic), *The spinless modular bootstrap at large central charge*, version 1 (November 2026), [§6.8, quantitative rate, p. 36](https://hexagonmath.org/pdf/2611.00174v1#page=36).
