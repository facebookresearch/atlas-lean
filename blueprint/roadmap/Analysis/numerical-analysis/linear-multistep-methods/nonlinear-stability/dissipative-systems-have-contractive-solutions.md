# Solutions of a dissipative system are contractive

If the system $y' = f(x, y)$ is [dissipative](dissipative-system.md) on $[x_0, \infty)$, then any two of its solutions $u$ and $v$ on $[x_0, \infty)$ are [contractive](contractive-solutions.md) in the Euclidean norm. The proof differentiates: $\frac12 \frac{d}{dx}\|u(x) - v(x)\|^2 = \langle f(x, u(x)) - f(x, v(x)), u(x) - v(x) \rangle \le 0$.

## Depends on

- [Dissipative system](dissipative-system.md)
- [Contractive solutions](contractive-solutions.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 5, the computation leading to (92) and the conclusion after Definition 15. <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
