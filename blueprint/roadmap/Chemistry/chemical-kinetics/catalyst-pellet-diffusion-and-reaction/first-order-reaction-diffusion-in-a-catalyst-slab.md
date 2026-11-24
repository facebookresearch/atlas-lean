# First-order reaction and diffusion in a catalyst slab

Consider an isothermal catalyst slab of thickness $2L$, $L > 0$, whose height and length are much larger
than its thickness, with effective diffusivity $D_A > 0$ and an irreversible first-order reaction of
rate constant $k \ge 0$. With $x$ the distance from the mid-plane and the surface concentration
$c_{As}$ held fixed, the steady concentration satisfies

$$D_A \, \frac{d^2 c_A}{dx^2} - k \, c_A = 0 \quad (0 < x < L), \qquad
\frac{dc_A}{dx}(0) = 0, \qquad c_A(L) = c_{As} .$$

Put $\Phi = L \sqrt{k / D_A}$ (the Thiele modulus of the slab, whose volume-to-surface ratio is $L$).
This boundary-value problem has the unique solution that is twice differentiable on $[0, L]$,

$$c_A(x) = c_{As} \, \frac{\cosh(\Phi x / L)}{\cosh \Phi}, \qquad 0 \le x \le L ;$$

for $k = 0$ it is the constant $c_{As}$.

Uniqueness: the difference $u$ of two solutions satisfies $D_A u'' = k u$, $u'(0) = 0$, $u(L) = 0$, and
multiplying by $u$ and integrating by parts gives $\int_0^L (D_A u'^2 + k u^2)\,dx = 0$, so $u' = 0$
and then $u = 0$.

## Depends on

## Proof depends on

## Sources

- J. B. Rawlings and J. G. Ekerdt, *Chemical Reactor Analysis and Design Fundamentals*, 2nd edition, paperback, seventh printing (November 2026), Nob Hill Publishing; freely distributed by the authors at <https://sites.engineering.ucsb.edu/~jbraw/chemreacfun/> (page numbers below are the printed ones): Section 7.4.2, Equations 7.34–7.35 with $q = 0$ (slab) and characteristic length $a = L$
  (pp. 370–371); Thiele modulus, Equation 7.18 (p. 363); Exercise 7.1 (pp. 416–417), whose
  dimensionless model $d^2 c_A / dx^2 - \Phi^2 c_A = 0$ on $[-1, 1]$ with $c_A = 1$ at $x = \pm 1$ is
  the symmetric form of this problem.
