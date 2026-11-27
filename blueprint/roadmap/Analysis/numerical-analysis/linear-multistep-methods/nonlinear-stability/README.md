# Nonlinear stability of multistep methods

Linear stability theory studies $y' = \lambda y$. For a nonlinear system $y' = f(y)$ whose vector field is dissipative, $\langle f(u) - f(v), u - v \rangle \le 0$, the distance between any two solutions does not increase. Dahlquist's G-stability asks the same of a multistep method: a G-stable one-leg method applied to a dissipative system produces numerical solutions that are contractive in a weighted norm on blocks of $k$ consecutive values. The one-leg twin maps solutions of the one-leg method to solutions of the linear multistep method, but it does not carry that contractivity over.

- [Contractive solutions](contractive-solutions.md)
- [Dissipative system](dissipative-system.md)
- [One-sided Lipschitz condition](one-sided-lipschitz-condition.md)
- [Solutions of a dissipative system are contractive](dissipative-systems-have-contractive-solutions.md)
- [One-leg twin of a linear multistep method](one-leg-twin.md)
- [Solutions of the one-leg twin give solutions of the multistep method](one-leg-twin-solutions-give-multistep-solutions.md)
- [G-stability](g-stability.md)
- [G-stable one-leg methods are contractive for dissipative systems](g-stable-one-leg-methods-are-contractive.md)

## Related topics

- [Absolute stability and A-stability](../absolute-stability-and-a-stability/README.md)
