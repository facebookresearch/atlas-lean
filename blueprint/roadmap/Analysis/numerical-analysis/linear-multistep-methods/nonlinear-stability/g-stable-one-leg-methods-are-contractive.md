# G-stable one-leg methods are contractive for dissipative systems

Let the autonomous system $y' = f(y)$ be [dissipative](dissipative-system.md), and let the [one-leg twin](one-leg-twin.md) $\rho(E) y_n = h\, s\, f(\sigma(E) y_n / s)$ of a linear multistep method with $s = \sigma(1) \ne 0$ be [G-stable](g-stability.md) with matrix $G$. If $(u_n)$ and $(v_n)$ are two solutions of the method, with blocks $U_n = (u_{n+k-1}^T, \dots, u_n^T)^T$ and $V_n$ likewise, then

$$\|U_{n+1} - V_{n+1}\|_G \le \|U_n - V_n\|_G \qquad \text{for all } n \ge 0,$$

the discrete counterpart of [contractivity of the exact solutions](dissipative-systems-have-contractive-solutions.md). The proof applies the G-stability inequality to $z_n = u_n - v_n$ and uses $\rho(E)(u_n - v_n) = h s\,[f(\sigma(E) u_n / s) - f(\sigma(E) v_n / s)]$, so that the right-hand side of the G-stability inequality is $2h \langle f(a) - f(b), a - b \rangle \le 0$ for $a = \sigma(E) u_n / s$ and $b = \sigma(E) v_n / s$, by dissipativity.

## Depends on

- [G-stability](g-stability.md)
- [Dissipative system](dissipative-system.md)
- [One-leg twin of a linear multistep method](one-leg-twin.md)

## Related topics

- [Solutions of a dissipative system are contractive](dissipative-systems-have-contractive-solutions.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 5, the computation after Definition 17 ending in $\|U_{n+1} - V_{n+1}\|_G^2 \le \|U_n - V_n\|_G^2$. <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
