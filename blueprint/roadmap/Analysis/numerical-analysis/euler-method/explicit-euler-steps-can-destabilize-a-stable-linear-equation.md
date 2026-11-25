# Explicit Euler steps can destabilize a stable linear equation

Let $a > 0$. Every solution $x(t) = x_0 e^{-a t}$ of $x' = -a x$ tends to $0$ as $t \to \infty$. For a step size $h > 0$, the explicit Euler iterates $x_{n+1} = x_n - h a x_n$, $n \in \mathbb{N}$, are $x_n = (1 - h a)^n x_0$. They tend to $0$ for every $x_0$ if and only if $0 < h a < 2$. At $h a = 2$ they alternate, $x_n = (-1)^n x_0$, and for $h a > 2$ they satisfy $|x_n| \to \infty$ whenever $x_0 \ne 0$. So the stability condition $a > 0$ of the differential equation does not carry over unchanged to its discretization, whose condition is $|1 - h a| < 1$. Sampling the exact solution does not cause this: $x(nh) = (e^{-ah})^n x_0$ tends to $0$ for every $h > 0$; the change comes from replacing the flow by the Euler step.

## Background

- [First-order convergence of the explicit Euler method](explicit-euler-first-order-convergence.md): on a fixed finite interval the Euler iterates converge to the solution as $h \to 0$; the statement here concerns a fixed $h$ and $n \to \infty$.

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, University of Oxford, Section 2.5: for $y' = \lambda y$ with $\lambda < 0$, Euler's explicit method gives $y_n = (1 + \lambda h)^n y_0$, which tends to $0$ if and only if $\lambda h \in (-2, 0)$, the interval of absolute stability (pp. 19–20). <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
