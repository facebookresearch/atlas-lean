# The Lasry–Lions identity

For real numbers $m_1, m_2$ and vectors $a, b$ of a real inner product space,

$$\frac{m_1 - m_2}{2}\,(|a|^2 - |b|^2) - \langle a - b,\, m_1 a - m_2 b\rangle = -\frac{m_1 + m_2}{2}\,|a - b|^2 .$$

The 2013 notes print the right-hand side of this display (proof of Theorem 3.6, p. 15) as
$-\frac{\bar m}{2}|Du_1 - Du_2|^2$ with $\bar m = m_1 - m_2$. Expanding both sides gives the coefficient
$\frac{m_1 + m_2}{2}$ (take $m_1 = m_2 = 1$: the left-hand side is $-|a - b|^2$), which is what the
sign argument of the proof uses.

This is the pointwise identity in the proof that the mean field game system

$$-\partial_t u - \Delta u + \tfrac12 |Du|^2 = F(x, m), \qquad \partial_t m - \Delta m - \operatorname{div}(m\, Du) = 0,$$

$m(0) = m_0$, $u(T) = G(x, m(T))$, has at most one classical solution when $F$ is strictly monotone
and $G$ monotone (Cardaliaguet, Theorem 3.6). For two solutions, test the Fokker–Planck equation
for $m_1 - m_2$ with $u_1 - u_2$ and the Hamilton–Jacobi–Bellman equation for $u_1 - u_2$ with
$m_1 - m_2$. With $a = Du_1$, $b = Du_2$ and densities $m_1, m_2 \ge 0$, the identity turns the sum
into $\int\!\!\int (m_1 - m_2)(F(x, m_1) - F(x, m_2)) \le 0$, and monotonicity forces $m_1 = m_2$. See the
[system](mean-field-game-system.md) and its
[uniqueness theorem](mean-field-game-system-uniqueness.md).

## Background

- [Fokker–Planck equation](../../../Probability/stochastic-calculus/fokker-planck-equation/README.md):
  the forward equation of the system, transporting the distribution of players along the optimal
  drift $-Du$.
- [Viscosity solutions of Hamilton–Jacobi equations](../../../Analysis/partial-differential-equations/viscosity-solutions-of-hamilton-jacobi-equations/README.md):
  the backward equation of the system is a Hamilton–Jacobi–Bellman equation; in the first-order
  case of the theory it is solved in the viscosity sense.
- [Wasserstein distances](../../../MeasureTheory/optimal-transport/wasserstein-distances/README.md):
  the existence theory of the system measures the dependence of $F$ and $G$ on $m$ in the
  Kantorovich–Rubinstein distance $d_1$.

## Sources

- J.-M. Lasry and P.-L. Lions, "Mean field games", Japan. J. Math. 2 (2007), 229–260.
- P. Cardaliaguet, *Notes on Mean Field Games (from P.-L. Lions' lectures at Collège de France)*, version of 27 September 2013, §3.3, proof of Theorem 3.6.
