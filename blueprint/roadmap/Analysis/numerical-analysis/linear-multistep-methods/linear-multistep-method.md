# Linear multistep method

Consider the initial value problem $y' = f(x, y)$, $y(x_0) = y_0$, for a real-valued function $y$ on $[x_0, X_M]$, and the equally spaced mesh points $x_n = x_0 + nh$ with step $h > 0$. Let $k \ge 1$. A *linear $k$-step method* is given by real coefficients $\alpha_0, \dots, \alpha_k$ and $\beta_0, \dots, \beta_k$ with $\alpha_k \ne 0$ and $\alpha_0, \beta_0$ not both zero. From starting values $y_0, \dots, y_{k-1}$ it determines approximations $y_n \approx y(x_n)$ by

$$\sum_{j=0}^{k} \alpha_j y_{n+j} = h \sum_{j=0}^{k} \beta_j f(x_{n+j}, y_{n+j}), \qquad n = 0, 1, 2, \dots$$

The method is *explicit* if $\beta_k = 0$, so that $y_{n+k}$ is given by earlier values, and *implicit* if $\beta_k \ne 0$. Its *first* and *second characteristic polynomials* are

$$\rho(z) = \sum_{j=0}^{k} \alpha_j z^j, \qquad \sigma(z) = \sum_{j=0}^{k} \beta_j z^j.$$

Euler's explicit method $y_{n+1} - y_n = h f(x_n, y_n)$, the implicit Euler method $y_{n+1} - y_n = h f(x_{n+1}, y_{n+1})$ and the trapezium rule $y_{n+1} - y_n = \tfrac{h}{2}\bigl(f(x_{n+1}, y_{n+1}) + f(x_n, y_n)\bigr)$ are linear one-step methods.

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 3, equation (37) and the paragraph after it, Example 3, and Section 3.2 (the characteristic polynomials). <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
