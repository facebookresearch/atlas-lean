# Orders and zero-stability of the backward differentiation formulas

For $1 \le k \le 6$ the $k$-step [backward differentiation formula](backward-differentiation-formulas.md) has [order](../order-of-accuracy-and-error-constants.md) $k$, with the error constant $C_{k+1}$ below, and is zero-stable. For $k = 1, 2$ it is [A-stable](a-stability.md). For $3 \le k \le 6$ its region of [absolute stability](absolute-stability.md) contains the half-plane $\{\bar h : \operatorname{Re} \bar h < -a\}$ for the constant $a$ below, and it is [A(α)-stable](a-alpha-stability.md) with the angle $\alpha$ below. For $k = 5, 6$ it is moreover [stiffly stable](stiff-stability.md) with that $a$ and some $c > 0$. For $k = 3, 4$ it is not stiffly stable: the boundary locus $\bar h(\theta) = \rho(e^{i\theta})/\sigma(e^{i\theta})$ has $\operatorname{Re} \bar h(\theta) = (1 - \cos\theta)^2(1 - 4\cos\theta)/3$ for $k = 3$ and $-2(1 - \cos\theta)^3(1 + 3\cos\theta)/3$ for $k = 4$, which are negative for small $\theta \ne 0$ while $\operatorname{Im} \bar h(\theta) \to 0$, so every rectangle $\{-a \le \operatorname{Re} \bar h < 0,\ |\operatorname{Im} \bar h| \le c\}$ contains points outside the region, such as $\bar h = -0.001 + 0.3i$ for $k = 3$ and $\bar h = -0.0001 + 0.3i$ for $k = 4$. For $k \ge 7$ the backward differentiation formula of order $k$ is not zero-stable.

| $k$ | $C_{k+1}$ | $a$ (stable for $\operatorname{Re} \bar h < -a$) | $\alpha$ in A(α)-stability |
|---|---|---|---|
| 1 | $-\tfrac12$ | A-stable | A-stable |
| 2 | $-\tfrac29$ | A-stable | A-stable |
| 3 | $-\tfrac3{22}$ | $0.1$ | $86^\circ$ |
| 4 | $-\tfrac{12}{125}$ | $0.7$ | $73^\circ$ |
| 5 | $-\tfrac{10}{137}$ | $2.4$ | $51^\circ$ |
| 6 | $-\tfrac{20}{343}$ | $6.1$ | $17^\circ$ |

The largest angles of A(α)-stability are $86.03^\circ$, $73.35^\circ$, $51.84^\circ$ and $17.84^\circ$ for $k = 3, \dots, 6$, rounded down here. The error constants are those of the normalization $\alpha_k = 1$; for $\sigma(1) = 1$ they are $C_{k+1}/\beta_k = -1/(k + 1)$.

## Depends on

- [Absolute stability of a linear multistep method](absolute-stability.md)
- [Backward differentiation formulas](backward-differentiation-formulas.md)
- [Zero-stability](../zero-stability.md)
- [Stiff stability](stiff-stability.md)
- [A(α)-stability](a-alpha-stability.md)
- [Order of accuracy and error constants of a linear multistep method](../order-of-accuracy-and-error-constants.md)
- [A-stability](a-stability.md)

## Proof depends on

- [Order conditions](../order-conditions.md)
- [Zero-stability and the root condition](../zero-stability-iff-root-condition.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 4.2, Table 3 (coefficients, order, error constant and stability parameters for $k = 1, \dots, 6$) and the statement after it that for $p \ge 7$ these methods are not zero-stable. Table 3 lists $a$ as the stiff-stability constant also for $k = 3, 4$, and Exercise 27 asks to show that the method with $k = 3$ is stiffly stable; neither holds in the sense of Definition 13, as shown above, although the values of $a$ are valid half-plane bounds (the leftmost boundary points are $-1/12$ and $-2/3$). The angles $88^\circ$, $52^\circ$ and $19^\circ$ printed in Table 3 for $k = 3, 5, 6$ are too large: for $k = 3$, the boundary point $\bar h = \rho(e^{i\theta})/\sigma(e^{i\theta}) \approx -0.0761 + 1.0968i$ at $\theta \approx 53.78^\circ$ lies in the wedge $W_{88^\circ}$ but $\rho - \bar h \sigma$ has the root $e^{i\theta}$ on the unit circle. <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
- E. Hairer and G. Wanner, *Solving Ordinary Differential Equations II: Stiff and Differential-Algebraic Problems*, 2nd edition, Springer, 1996, Section V.2, (2.7), p. 251 (stability of the backward differentiation formulas), for the angles $86.03^\circ$, $73.35^\circ$, $51.84^\circ$ and $17.84^\circ$, which also follow from the boundary locus $\theta \mapsto \rho(e^{i\theta})/\sigma(e^{i\theta})$. <https://doi.org/10.1007/978-3-642-05221-7>
