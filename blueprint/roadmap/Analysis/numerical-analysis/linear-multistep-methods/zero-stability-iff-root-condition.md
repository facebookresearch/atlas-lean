# Zero-stability is equivalent to the root condition

A [linear multistep method](linear-multistep-method.md) is [zero-stable](zero-stability.md) for every differential equation $y' = f(x, y)$ whose right-hand side $f$ is continuous on a rectangle $R = \{(x, y) : x_0 \le x \le X_M,\ |y - y_0| \le Y_M\}$ and satisfies a Lipschitz condition $|f(x, y) - f(x, z)| \le L|y - z|$ on $R$, if and only if it satisfies the [root condition](root-condition.md): the zeros of its first characteristic polynomial $\rho$ lie in the closed unit disc and those on the unit circle are simple.

Necessity follows by applying the method to $y' = 0$: the general solution of $\sum_j \alpha_j y_{n+j} = 0$ is $\sum_s p_s(n) z_s^n$ over the zeros $z_s$ of $\rho$, with $\deg p_s$ one less than the multiplicity of $z_s$, and a zero with $|z_s| > 1$, or a multiple zero with $|z_s| = 1$, gives solutions that grow without bound as $h \to 0$ with $nh$ fixed.

## Depends on

- [Zero-stability](zero-stability.md)
- [Root condition](root-condition.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 3.2, Theorem 6 with its proof of necessity; the proof of sufficiency is referred there to P. Henrici, *Discrete Variable Methods in Ordinary Differential Equations*, Wiley, 1962. <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
