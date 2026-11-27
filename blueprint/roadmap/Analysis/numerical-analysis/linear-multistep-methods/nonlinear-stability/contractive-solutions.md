# Contractive solutions

Let $u$ and $v$ be two solutions of the differential equation $y' = f(x, y)$ in $\mathbb{R}^m$ on $[x_0, \infty)$, with initial values $u(x_0) = u_0$ and $v(x_0) = v_0$. They are *contractive* in the Euclidean norm $\|\cdot\|$ if

$$\|u(x_2) - v(x_2)\| \le \|u(x_1) - v(x_1)\| \qquad \text{for all } x_2 \ge x_1 \ge x_0 .$$

For a linear system $y' = Ay$ whose eigenvalues all have negative real part this holds, for example, when $A$ is normal (a sufficient condition), by $\|u(x_2) - v(x_2)\| \le e^{(x_2 - x_1)\max_i \Re\lambda_i(A)}\|u(x_1) - v(x_1)\|$.

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 5, inequality (91) and Definition 14. The definition there prints $\|u(x_2) - v(x_1)\|$ on the left; the intended quantity is $\|u(x_2) - v(x_2)\|$. Inequality (91) is stated there for any $A$ with eigenvalues of negative real part, but in the Euclidean norm it needs a normal $A$; a nonnormal $A$ can make $\|u - v\|$ grow transiently. <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
