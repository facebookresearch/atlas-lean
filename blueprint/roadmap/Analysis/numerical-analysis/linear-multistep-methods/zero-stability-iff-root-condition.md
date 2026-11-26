# Zero-stability is equivalent to the root condition

A [linear multistep method](linear-multistep-method.md) is [zero-stable](zero-stability.md) for every differential equation $y' = f(x, y)$ on $[x_0, X_M]$ whose right-hand side $f$ is continuous on $[x_0, X_M] \times \mathbb{R}$ and satisfies a Lipschitz condition $|f(x, y) - f(x, z)| \le L|y - z|$ for all $x \in [x_0, X_M]$ and all real $y, z$, if and only if it satisfies the [root condition](root-condition.md): the zeros of its first characteristic polynomial $\rho$ lie in the closed unit disc and those on the unit circle are simple.

Necessity follows by applying the method to $y' = 0$. For a nonzero zero $z_s$ of $\rho$ of multiplicity $m_s$, the sequences $n^j z_s^n$, $0 \le j < m_s$, solve $\sum_j \alpha_j y_{n+j} = 0$ (the zero $0$ contributes only solutions that vanish after finitely many terms), and a zero with $|z_s| > 1$, or a multiple zero with $|z_s| = 1$, gives solutions that grow without bound as $h \to 0$ with $nh$ fixed.

## Depends on

- [Zero-stability](zero-stability.md)
- [Root condition](root-condition.md)
- [Linear multistep method](linear-multistep-method.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 3.2, Theorem 6 with its proof of necessity; the proof of sufficiency is referred there to P. Henrici, *Discrete Variable Methods in Ordinary Differential Equations*, Wiley, 1962. The notes state the Lipschitz condition on a rectangle $|y - y_0| \le Y_M$. For an implicit method that does not control the computed values, which may leave the rectangle: implicit Euler for $y' = y^2$, $y(0) = 0$, has besides $y_n = 0$ the solution with $y_n = 0$ for $n < N$ and $y_N = 1/h$. So a global Lipschitz condition is used here, with steps $h|\beta_k| L < |\alpha_k|$ for which each implicit equation has exactly one solution. <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
