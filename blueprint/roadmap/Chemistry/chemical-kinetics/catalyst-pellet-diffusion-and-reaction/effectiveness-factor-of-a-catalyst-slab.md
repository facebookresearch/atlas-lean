# Effectiveness factor of a catalyst slab

For the [first-order catalyst slab](first-order-reaction-diffusion-in-a-catalyst-slab.md) with $k > 0$, $c_{As} > 0$ and Thiele
modulus $\Phi = L\sqrt{k/D_A} > 0$, the effectiveness factor, the ratio of the slab's mean reaction
rate to the rate at the surface concentration,

$$\eta = \frac{1}{L} \int_0^L \frac{k\, c_A(x)}{k\, c_{As}} \, dx,$$

equals

$$\eta = \frac{\tanh \Phi}{\Phi} .$$

The same value is obtained from the surface flux, $\eta = (D_A / (k L c_{As})) \, c_A'(L)$, since
integrating the steady balance over $[0, L]$ equates the total reaction rate with the flux through the
surface.

The function $g(\Phi) = \tanh \Phi / \Phi$ on $\Phi > 0$ satisfies $0 < g(\Phi) < 1$, and
$\Phi \, g(\Phi) \to 1$ as $\Phi \to \infty$ (the diffusion-limited asymptote $\eta \sim 1/\Phi$).
It extends continuously to $\Phi = 0$ with value $1$; this extension is the rate-limited limit of
$\eta$ as $\Phi \to 0^+$, not an evaluation of the defining ratio, which is $0/0$ at $k = 0$.

## Depends on

- [First-order reaction and diffusion in a catalyst slab](first-order-reaction-diffusion-in-a-catalyst-slab.md), which defines $c_A$

## Proof depends on

## Sources

- J. B. Rawlings and J. G. Ekerdt, *Chemical Reactor Analysis and Design Fundamentals*, 2nd edition, paperback, seventh printing (November 2026), Nob Hill Publishing; freely distributed by the authors at <https://sites.engineering.ucsb.edu/~jbraw/chemreacfun/> (page numbers below are the printed ones): Section 7.4.2, Table 7.3, Equation 7.40 (slab, $\eta = \tanh\Phi/\Phi$, p. 372) and the
  integral and flux forms of the effectiveness factor, Equations 7.36–7.37 (p. 371); Exercise 7.1(d)
  (p. 417).
