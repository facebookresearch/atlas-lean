# Free-molecular flat-plate coefficients in the hypersonic limit

A body flies in the *free-molecular* regime when the molecular mean free path is much larger than the body, so incident and reflected molecules do not collide near it. Consider a flat plate of area $A$ (one side) at angle of attack $\alpha \in [0, \pi/2]$ in a stream of density $\rho$ and speed $U$. Two models of gas–surface interaction are used:
- *specular reflection*: each molecule leaves with its velocity component normal to the plate reversed and its tangential component unchanged;
- *diffuse reflection*: molecules are re-emitted in random directions.

Let the *speed ratio* $s$ be the stream speed divided by the most probable thermal speed of the molecules. Coefficients are referred to the dynamic pressure $\tfrac12\rho U^2$ and the area $A$.

**Theorem.** For specular reflection, as $s \to \infty$, the free-molecular flat-plate coefficients tend to the values

$$
C_D = 4\sin^3\alpha, \qquad C_L = 4\sin^2\alpha\cos\alpha,
$$

and, for $0 < \alpha \le \pi/2$, the lift-to-drag ratio is $L/D = \cot\alpha$. At $\alpha = 0$ both coefficients vanish and the ratio is undefined.
If the molecules instead lose their normal momentum and keep their tangential velocity, which is Newtonian impact theory for hypersonic continuum flow, the coefficients are half of these.

**Proof in the cold-beam limit.** As $s \to \infty$, the thermal spread is negligible, and every molecule arrives with velocity $U$. The mass flux onto the plate per unit area is $\rho U\sin\alpha$, and each molecule carries normal velocity $U\sin\alpha$ toward the plate. Specular reflection reverses this, so the plate receives normal momentum $2\rho U^2\sin^2\alpha$ per unit area and time, and no tangential momentum. The normal force is $N = 2\rho U^2\sin^2\alpha\,A$, so $C_N = 4\sin^2\alpha$. Resolving along and across the stream gives $C_D = C_N\sin\alpha$ and $C_L = C_N\cos\alpha$. If the normal momentum is only destroyed rather than reversed, the transfer halves.

For finite $s$, the coefficients involve $\exp(-s^2\sin^2\alpha)$ and $\operatorname{erf}(s\sin\alpha)$. Diffuse reflection gives larger drag at small $\alpha$, because the tangential momentum is also absorbed. Rarefied entry analysis beyond this idealization needs a kinetic model valid between the free-molecular and continuum regimes, and needs gas–surface accommodation coefficients.

## Background

- [Ballistic entry constant](ballistic-k.md)
- [Stagnation-point heating correlation with a validity box](stagnation-heating-correlation.md)

## Sources

- J. R. Stalder and V. J. Zurick, *Theoretical Aerodynamic Characteristics of Bodies in a Free-Molecule-Flow Field*, NACA Technical Note 2423, 1951, full text <https://archive.org/stream/NASA_NTRS_Archive_19930083019/NASA_NTRS_Archive_19930083019_djvu.txt>:
    - Summary and Introduction: the free-molecule regime, a Maxwellian thermal velocity superimposed on the mass velocity, the speed ratio $s$, and the definitions of diffuse and specular reflection;
    - the reflection model analogous to hypersonic flow, which gives half the specular coefficients;
    - the flat-plate coefficients (A3)–(A4), and their limits as $s \to \infty$ for specular reflection, $C_D = 4\sin^3\alpha$, $C_L = 4\sin^2\alpha\cos\alpha$ (Newtonian flow), with $L/D = \cot\alpha$.
