# The one-third power law is motion at constant equi-affine speed

Let $x : [t_0, t_1] \to \mathbb{R}^2$ be a $C^2$ planar hand trajectory with Euclidean speed $v(t) = |\dot x(t)| > 0$ and Euclidean curvature $\kappa(t) > 0$ (a convex stroke). Its **equi-affine arc length** and **equi-affine speed** are

$$\sigma(t) = \int_{t_0}^{t} \kappa^{1/3}\, ds = \int_{t_0}^{t} \big|\det(\dot x(\tau), \ddot x(\tau))\big|^{1/3} d\tau, \qquad \dot\sigma = \kappa^{1/3} v = \big|\det(\dot x, \ddot x)\big|^{1/3},$$

where $s$ is Euclidean arc length. Both are invariant under equi-affine maps $x \mapsto M x + c$ with $\det M = 1$.

**Proposition (Sect. 3.5 of the source).** On any time interval and for any constant $G > 0$ the following are equivalent:

1. the equi-affine speed is constant, $\dot\sigma \equiv G$;
2. the one-third power law holds, $v = G\, \kappa^{-1/3} = G\, \rho^{1/3}$ with $\rho = 1/\kappa$ the radius of curvature;
3. the two-thirds power law holds, $A = \kappa v = G\, \kappa^{2/3}$, where $A$ is the angular velocity of the tangent;
4. $\kappa v^3 \equiv G^3$.

## Expansion

The identity $|\det(\dot x, \ddot x)| = \kappa v^3$ gives $\dot\sigma = \kappa^{1/3} v$, and the four statements are rearrangements of $\kappa^{1/3} v = G$. The empirical two-thirds power law of drawing and handwriting (Lacquaniti, Terzuolo and Viviani 1983) thus says that curved strokes are generated at piecewise constant equi-affine speed, with $G$ changing between segments. The source argues from this that the motor system represents movement in equi-affine rather than Euclidean geometry, and shows that local isochrony and the time-scaling property of movements are compatible with a piecewise constant $\dot\sigma$. The equi-affine geodesics are the parabolas, whose affine length is fixed by their support triangle.

## Sources

- T. Flash and A. A. Handzel, *Affine differential geometry analysis of human arm movements*, Biological Cybernetics 96(6) (2007), 577-601. DOI: <https://doi.org/10.1007/s00422-007-0145-5>. PMCID: PMC2799626.
- F. Lacquaniti, C. Terzuolo and P. Viviani, *The law relating the kinematic and figural aspects of drawing movements*, Acta Psychologica 54 (1983), 115-130.
