# Diagonal stability and global stability of Lotka–Volterra equilibria

For the generalized Lotka–Volterra system $\dot x_i = x_i (r_i + (Ax)_i)$, $i = 1, \dots, n$, on the open positive orthant, suppose there is an interior equilibrium $x^* > 0$ and a positive diagonal matrix $W = \operatorname{diag}(w_1, \dots, w_n)$ with $WA + A^\top W$ negative definite ($A$ is Lyapunov diagonally stable). Then Goh's function $V(x) = \sum_i w_i (x_i - x_i^* - x_i^* \ln(x_i/x_i^*))$ is nonnegative, vanishes only at $x^*$, and satisfies

$$\dot V = \tfrac12 (x - x^*)^\top (WA + A^\top W)(x - x^*) < 0 \qquad (x \ne x^*),$$

so $x^*$ is globally asymptotically stable in the open positive orthant: it is stable, and every solution starting in the open orthant converges to $x^*$ (Goh 1977). The identity uses $r = -Ax^*$: $\dot V = \sum_i w_i (x_i - x_i^*)(r_i + (Ax)_i) = \sum_i w_i (x_i - x_i^*)(A(x - x^*))_i$.

## Depends on

- [Generalized Lotka–Volterra vector field](../../replicator-and-lotka-volterra-equivalence/lv-field.md)

## Proof depends on

- [LaSalle's invariance principle](../../../../Dynamics/smooth-dynamics/lasalle-s-invariance-principle/lasalle.md)

## Expansion

1. The model on the open orthant, invariance of the orthant, and interior equilibria.
2. The function $V$: nonnegativity from $z - 1 - \ln z \ge 0$, $V(x) = 0$ only at $x^*$, and properness on the open orthant.
3. The derivative identity, using $r = -Ax^*$.
4. Global attraction from $\dot V < 0$ off $x^*$ and properness (or LaSalle's invariance principle).
5. Uniqueness of the interior equilibrium under the hypothesis, and local stability of feasible equilibria for D-stable $A$, as separate statements.

## Sources

- Original result: B. S. Goh, Global stability in many-species systems, Am. Nat. 111 (1977), 135–143. <https://doi.org/10.1086/283144>
