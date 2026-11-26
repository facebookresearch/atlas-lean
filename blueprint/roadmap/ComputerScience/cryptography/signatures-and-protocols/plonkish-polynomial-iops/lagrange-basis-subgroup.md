# Lagrange basis over a multiplicative subgroup

For $H=\langle\omega\rangle$ of order $n$ (with $n$ invertible in $\mathbb{F}$), the Lagrange polynomials

$$
L_i(X)=\frac{\omega^{i}\,(X^{n}-1)}{n\,(X-\omega^{i})},\qquad 0\le i< n,
$$

satisfy $L_i(\omega^{j})=\delta_{ij}$, form a basis of polynomials of degree $< n$, and can each be evaluated at a point $\zeta\notin H$ with $O(\log n)$ field operations. In particular $\sum_iL_i=1$ and the verifier evaluates the public-input polynomial $PI(\zeta)=\sum_{i<\ell}x_iL_i(\zeta)$ in $O(\ell+\log n)$ operations.

## Proof sketch

$(X^{n}-1)/(X-\omega^{i})=\prod_{j\ne i}(X-\omega^{j})$, whose value at $\omega^{i}$ is the derivative $n\omega^{i(n-1)}=n\omega^{-i}$; multiplying by $\omega^{i}/n$ normalizes it to $1$. Evaluating at $\zeta$ needs $\zeta^{n}$ by repeated squaring and one inversion.

## Depends on

- [PLONK gate equations with copy constraints](plonk-constraint-system.md)

## Sources

- Ariel Gabizon, Zachary J. Williamson, Oana Ciobotaru, "PLONK: Permutations over Lagrange-bases for Oecumenical Noninteractive arguments of Knowledge", IACR ePrint 2019/953 (2019).
