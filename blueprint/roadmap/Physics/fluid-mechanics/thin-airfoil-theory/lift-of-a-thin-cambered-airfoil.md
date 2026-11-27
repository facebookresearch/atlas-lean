# Lift of a thin cambered airfoil

This node covers the classical result of thin-airfoil theory. Consider steady incompressible inviscid flow with free-stream speed
$U > 0$ past a thin airfoil of chord $c$ at small angle of attack $\alpha$, whose mean camber line $z(x)$, $0 \le x \le c$, is
continuously differentiable with $z(0) = z(c) = 0$. Represent the airfoil by a vortex sheet on the chord, impose flow tangency to the camber
line to first order and the Kutta condition at the trailing edge. With $x = \tfrac c2(1 - \cos\theta_0)$, the sectional lift coefficient is

$$c_l = 2\pi(\alpha - \alpha_{L=0}), \qquad \alpha_{L=0} = -\frac1\pi\int_0^\pi \frac{dz}{dx}\,(\cos\theta_0 - 1)\,d\theta_0 .$$

In particular the lift slope is $2\pi$ per radian and a symmetric airfoil has $\alpha_{L=0} = 0$.

## Expansion

A good expansion states the linearized boundary problem, solves the integral equation for the vortex strength in its Fourier
form under the Kutta condition, and derives the lift by the Kutta-Joukowski theorem. Prandtl's lifting-line theory for a finite wing,
with elliptic loading giving $C_L = a_0\alpha/(1 + a_0/(\pi A))$ and induced drag $C_L^2/(\pi A)$ for aspect ratio $A$, is a separate node.

## Sources

- J. D. Anderson, *Fundamentals of Aerodynamics*, 3rd edition, McGraw-Hill, 2001, for thin-airfoil and lifting-line theory.
