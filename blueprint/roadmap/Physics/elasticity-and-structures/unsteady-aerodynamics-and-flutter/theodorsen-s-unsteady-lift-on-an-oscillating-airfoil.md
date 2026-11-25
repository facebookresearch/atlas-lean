# Theodorsen's unsteady lift on an oscillating airfoil

This node covers Theodorsen's linearized unsteady lift. Consider a flat-plate airfoil of semichord $b > 0$ in incompressible inviscid
flow of speed $U > 0$ and density $\rho$, performing small harmonic plunge $h(t) = \operatorname{Re}(\bar h\,e^{i\omega t})$ and pitch $\alpha(t) = \operatorname{Re}(\bar\alpha\,e^{i\omega t})$,
with complex amplitudes $\bar h, \bar\alpha$, about an axis at $x = ab$ measured from midchord, at reduced frequency $k = \omega b/U > 0$,
with a planar wake and the Kutta condition. Then the lift per unit span is $L(t) = \operatorname{Re}(\bar L\,e^{i\omega t})$ with complex
amplitude

$$\bar L = \pi\rho b^2\big(-\omega^2\bar h + i\omega U\bar\alpha + ab\,\omega^2\bar\alpha\big) + 2\pi\rho U b\,C(k)\Big[i\omega\bar h + U\bar\alpha + i\omega b\big(\tfrac12 - a\big)\bar\alpha\Big],$$

with $h$ positive downward and Theodorsen's function $C(k) = H_1^{(2)}(k)/\big(H_1^{(2)}(k) + i H_0^{(2)}(k)\big)$, where $H_n^{(2)}$ are Hankel
functions of the second kind.

## Expansion

A good expansion fixes the sign conventions, states the linearized potential problem with the shed planar wake, separates the
noncirculatory and circulatory parts, and evaluates the wake integral to obtain $C(k)$. The pitching moment, flutter determinants for a typical
section, strip theory and nonlinear limit cycles are separate nodes.

## Sources

- T. Theodorsen, General theory of aerodynamic instability and the mechanism of flutter, NACA Report 496, 1935.
- T. H. G. Megson, *Aircraft Structures for Engineering Students*, 5th edition, Butterworth-Heinemann, 2012, for elementary aeroelasticity.
