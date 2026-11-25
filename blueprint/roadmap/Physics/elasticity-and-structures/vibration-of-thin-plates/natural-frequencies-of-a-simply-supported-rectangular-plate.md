# Natural frequencies of a simply supported rectangular plate

This node covers the free vibration of a Kirchhoff plate. Let a homogeneous isotropic plate occupy $[0, a] \times [0, b]$, with thickness
$h > 0$, density $\rho > 0$ and flexural rigidity $D = Eh^3/(12(1 - \nu^2))$, where $E > 0$ and $-1 < \nu < 1/2$, and let its transverse
deflection satisfy $D\,\Delta^2 w + \rho h\,w_{tt} = 0$ with simply supported edges ($w = 0$ and zero normal bending moment). Then the
separated solutions $w = \sin(m\pi x/a)\sin(n\pi y/b)\cos(\omega t)$, $m, n \ge 1$, are normal modes, every normal mode is a finite linear
combination of separated solutions with a common frequency (distinct $(m, n)$ can share one, for example when $a = b$), and the frequencies are

$$\omega_{mn} = \pi^2\left(\frac{m^2}{a^2} + \frac{n^2}{b^2}\right)\sqrt{\frac{D}{\rho h}},$$

and these modes form a complete orthogonal system in $L^2([0, a] \times [0, b])$.

## Expansion

A good expansion states the Kirchhoff plate model and its simply supported boundary conditions as model inputs, verifies the
modes and frequencies, and proves completeness from the completeness of the product sine basis. Timoshenko beams, other boundary
conditions, and shells are separate nodes.

## Sources

- A. W. Leissa, *Vibration of Plates*, NASA SP-160, 1969, for the simply supported rectangular plate.
- T. H. G. Megson, *Aircraft Structures for Engineering Students*, 5th edition, Butterworth-Heinemann, 2012, for the bending theory of thin plates.
