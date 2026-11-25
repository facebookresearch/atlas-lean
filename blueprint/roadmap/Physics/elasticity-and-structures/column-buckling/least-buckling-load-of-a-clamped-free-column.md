# Least buckling load of a clamped-free column

This node covers the sharp characterization of the Euler load of a cantilever column. Let a column of length $L > 0$ have constant
bending stiffness $EI > 0$, be clamped at $x = 0$ and free at $x = L$, and carry an axial compressive load $P \ge 0$. On the admissible space
$\{w \in H^2(0, L) : w(0) = w'(0) = 0\}$ the second variation of the potential energy is

$$\delta^2\Pi(w) = \int_0^L \big(EI\,(w'')^2 - P\,(w')^2\big)\,dx .$$

It is positive for every nonzero admissible $w$ if and only if $P < P_{\mathrm{cr}} = \pi^2 EI/(4L^2)$, and at $P = P_{\mathrm{cr}}$ it vanishes
exactly on the multiples of $w(x) = 1 - \cos(\pi x/(2L))$.

## Expansion

A good expansion proves the sharp inequality $\int_0^L (w'')^2 \ge \tfrac{\pi^2}{4L^2}\int_0^L (w')^2$ on the admissible space, for
example by expanding $w'$ in the eigenfunctions of the corresponding mixed Sturm-Liouville problem, and identifies its equality case. The
clamped-clamped column, with $P_{\mathrm{cr}} = 4\pi^2 EI/L^2$, is a separate node with its own variational inequality.

## Sources

- T. H. G. Megson, *Aircraft Structures for Engineering Students*, 5th edition, Butterworth-Heinemann, 2012, for the Euler buckling of columns with various end conditions.
