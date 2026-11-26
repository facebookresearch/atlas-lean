# The θ-method

For the initial value problem $y' = f(x, y)$, $y(x_0) = y_0$, on $[x_0, X_M]$ with mesh points $x_n = x_0 + nh$, $h = (X_M - x_0)/N$, and a parameter $\theta \in [0, 1]$, the *θ-method* is

$$y_{n+1} = y_n + h\big[(1 - \theta) f(x_n, y_n) + \theta f(x_{n+1}, y_{n+1})\big], \qquad n = 0, \dots, N - 1 .$$

It is the explicit Euler method for $\theta = 0$, the implicit Euler method for $\theta = 1$ and the trapezium rule for $\theta = 1/2$; it is explicit only for $\theta = 0$. It comes from approximating $\int_{x_n}^{x_{n+1}} f(x, y(x))\,dx$ by $h[(1 - \theta) f(x_n, y(x_n)) + \theta f(x_{n+1}, y(x_{n+1}))]$.

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 2.1, the integral identity (14), the method (16) and the remarks after it. <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
