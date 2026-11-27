# Fourier solution of the Airy equation

For $u_0 : \mathbb{R} \to \mathbb{C}$, let
$\widehat{u_0}(\xi) = (2\pi)^{-1/2} \int_{\mathbb{R}} u_0(y) e^{-iy\xi}\,dy$ be its unitary
Fourier transform. The Airy solution with initial datum $u_0$ is the function
$u : \mathbb{R}^2 \to \mathbb{C}$ given by

$$u(t, x) = (2\pi)^{-1/2} \int_{\mathbb{R}} e^{i(t\xi^3 + x\xi)}\, \widehat{u_0}(\xi)\,d\xi,$$

where an integral whose integrand is not integrable is taken to be $0$.

For $u_0 \in C_c^\infty(\mathbb{R})$ this function solves the Airy equation
$\partial_t u + \partial_x^3 u = 0$ with $u(0, \cdot) = u_0$.
