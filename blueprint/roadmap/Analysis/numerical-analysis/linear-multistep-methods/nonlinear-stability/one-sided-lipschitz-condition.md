# One-sided Lipschitz condition

A function $f : [x_0, \infty) \times \mathbb{R}^m \to \mathbb{R}^m$ satisfies a *one-sided Lipschitz condition* on $[x_0, \infty)$ if there is a function $\nu : [x_0, \infty) \to \mathbb{R}$ with

$$\langle f(x, u) - f(x, v),\ u - v \rangle \le \nu(x)\, \|u - v\|^2 \qquad \text{for all } x \ge x_0 \text{ and } u, v \in \mathbb{R}^m .$$

If $\nu(x) \le 0$ for all $x$, the system $y' = f(x, y)$ is [dissipative](dissipative-system.md). A function Lipschitz in $u$ with constant $L$ satisfies it with $\nu = L$, but the best $\nu$ can be far smaller than $L$, and negative.

## Depends on

- [Dissipative system](dissipative-system.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 5, Definition 16, inequality (94), and the remark after it. <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
