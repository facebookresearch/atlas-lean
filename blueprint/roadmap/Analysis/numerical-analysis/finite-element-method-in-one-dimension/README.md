# Finite element method in one dimension

- [Length of a mesh element](width.md)
- [Slope of a P1 function on a mesh element](element-slope.md)
- [Clamped ramp function of a mesh element](ramp.md)
- [Continuous piecewise linear function with given nodal values](p1.md)
- [Hat function of a mesh node](hat.md)
- [Nodal interpolant of a function](interp.md)
- [Linear map from nodal values to P1 functions](p1-map.md)
- [Nodal vectors with zero boundary values](dirichlet-nodal.md)
- [P1 finite element space with zero boundary values](p1-space.md)
- [Energy form of the equation $-u'' = f$](energy.md)
- [Element vector of the stiffness assembly](element-vector.md)
- [Assembled stiffness matrix of the P1 method](stiffness.md)
- [Load vector of the P1 method](load.md)
- [Classical solution of the Dirichlet problem $-u'' = f$](is-classical-solution.md)
- [Classical solutions satisfy the equation on the closed interval](eq-icc.md)
- [Solution of the Galerkin system](is-galerkin-solution.md)

## The P1 functions

- [Mesh elements have positive length](width-pos.md)
- [Element lengths are bounded by the mesh size](width-le-mesh.md)
- [P1 functions are linear on each element](p1-eq-of-mem-icc.md)
- [P1 functions interpolate their nodal values](p1-points.md)
- [Continuity of P1 functions](continuous-p1.md)
- [Derivative of a P1 function inside an element](has-deriv-at-p1.md)
- [Integral over the unit interval as a sum over elements](integral-eq-sum.md)
- [Energy pairing with a P1 function via nodal differences](energy-p1.md)

## Weak form, stiffness matrix, Galerkin orthogonality

- [Characterization of membership in the P1 space](mem-p1-space.md)
- [Interior hat functions lie in the P1 space](hat-mem-p1-space.md)
- [Weak form of the classical solution for $C^1$ test functions](energy-eq-integral-mul-of-cont-diff.md)
- [Weak form of the classical solution for P1 test functions](energy-eq-integral-mul-of-mem-p1-space.md)
- [Energy form of two P1 functions](energy-p1-p1.md)
- [Quadratic form of the stiffness matrix](dot-product-stiffness-mul-vec.md)
- [Stiffness matrix is the Gram matrix of the hat functions](energy-hat-hat.md)
- [Off-diagonal stiffness entry of an element](stiffness-cast-succ-succ.md)
- [Diagonal stiffness entry at an interior node](stiffness-succ-succ.md)
- [Tridiagonality of the stiffness matrix](stiffness-eq-zero.md)
- [Nodal values of the exact solution solve the Galerkin system](is-galerkin-solution-nodal.md)
- [Uniqueness of the Galerkin solution](is-galerkin-solution-unique.md)
- [In one dimension the Galerkin solution is the nodal interpolant](p1-eq-interp-of-is-galerkin-solution.md)
- [Galerkin orthogonality](galerkin-orthogonality.md)
- [Element-wise energy of a function minus a P1 function](energy-sub-p1-self.md)
- [Best approximation](energy-sub-galerkin-le.md)

## Error estimates

- [Wirtinger's inequality on an interval](integral-sq-le-of-eq-zero.md)
- [Element estimate for $C^2$ functions vanishing at both ends](integral-deriv-sq-le-of-eq-zero.md)
- [Interpolation estimate](energy-sub-interp-le.md)
- [Energy error estimate](energy-sub-galerkin-le-mesh.md)
- [Energy error estimate for the P1 Galerkin solution](sqrt-energy-sub-galerkin-le-mesh.md)
- [`L²` error estimate](integral-sq-sub-galerkin-le-mesh.md)
