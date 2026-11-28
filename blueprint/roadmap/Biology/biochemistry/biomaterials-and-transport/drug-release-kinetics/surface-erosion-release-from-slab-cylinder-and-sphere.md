# Surface-erosion release from a slab, cylinder or sphere

If a uniformly loaded device releases drug only as its surface recedes at constant speed, the released fraction is $1 - (1 - k_0t/(C_0a))^n$ with $n = 1, 2, 3$ for a slab, an infinite cylinder and a sphere; only the slab, whose area is constant, releases linearly.

Let drug be uniform at concentration $C_0 > 0$ in a slab of half-thickness $a$ (per unit area), an infinitely long cylinder of radius $a$ (per unit length) or a sphere of radius $a$, with $a > 0$. Suppose the body erodes only at its surface, which recedes at constant normal speed $v = k_0/C_0$ ($k_0 > 0$ the drug mass released per unit area per unit time), and that drug is released exactly as material is removed. Then

$$\frac{M_t}{M_\infty} = 1 - \left(1 - \frac{k_0 t}{C_0 a}\right)^{n}, \qquad 0 \le t \le t_f = \frac{C_0 a}{k_0}, \qquad n = 1, 2, 3,$$

and $M_t/M_\infty = 1$ for $t \ge t_f$. For the slab this is $t/t_f$ (zero order); for the sphere the release rate $(3/t_f)(1 - t/t_f)^2$ decreases with time.

## Context

Undergraduate. Li and Mooney explain when erosion is surface-limited (bond cleavage faster than transport of water or enzyme into the bulk) and say mass loss can be fairly linear for surface-eroding gels, giving near zero-order release; the formula shows that exact linearity requires a fixed eroding area (slab) or holds only at short times for shrinking cylinders and spheres. For a finite cylinder of radius $r_0$ and height $2h_0$ eroding on all faces, the remaining volume fraction is $(1 - vt/r_0)^2(1 - vt/h_0)$ until either factor first vanishes, at $t = \min(r_0, h_0)/v$, and zero thereafter; the open copy's Eq. (47) prints a square on both factors, which is not adopted here. Mircioiu et al. note that Hopfenberg's formula generalizes the Hixson–Crowell cube-root law.

## Depends on

None.

## Proof depends on

None.

## Expansion

The remaining volume fraction is $(r(t)/a)^n$ with $r(t) = a - vt$, $n$ the number of eroding dimensions; differentiate for the release rate. A page for the finite cylinder (with the correct exponent and the time of first exhaustion) and a page coupling erosion with interior diffusion are still needed.

## Sources

- C. Mircioiu, V. Voicu, V. Anuta, A. Tudose, C. Celia, D. Paolino, M. Fresta, R. Sandulovici and I. Mircioiu, "Mathematical Modeling of Release Kinetics from Supramolecular Drug Delivery Systems", Pharmaceutics 11(3), 140 (2019), <https://doi.org/10.3390/pharmaceutics11030140>; open-access copy read at <https://pmc.ncbi.nlm.nih.gov/articles/PMC6471682/>: Section 3.3: constant erosion rate assumption and Eqs. (42)–(46) for sheet and sphere; Section 3.3.3, Eq. (47), whose printed exponent is corrected here; Section 3.3.4, Eq. (48) (Hopfenberg model with $n = 3, 2, 1$) and the remark on Hixson–Crowell
- J. Li and D. J. Mooney, "Designing hydrogels for controlled drug delivery", Nature Reviews Materials 1, 16071 (2016), <https://doi.org/10.1038/natrevmats.2016.71>; author manuscript read at <https://pmc.ncbi.nlm.nih.gov/articles/PMC5898614/>: section on degradation-controlled release: bulk versus surface erosion and "fairly linear" mass loss for surface-eroding gels
