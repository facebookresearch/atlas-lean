# End forces and energy of a Hermite beam element

For an Euler–Bernoulli beam element of length $L > 0$ and constant $EI > 0$, with end displacements and rotations
$d = (v_1, \theta_1, v_2, \theta_2)$ interpolated by the Hermite cubic $y$, where $\theta_1=y'(0)$ and $\theta_2=y'(L)$,
the element stiffness matrix is

$$K_e = \frac{EI}{L^3}\begin{pmatrix} 12 & 6L & -12 & 6L \\ 6L & 4L^2 & -6L & 2L^2 \\ -12 & -6L & 12 & -6L \\ 6L & 2L^2 & -6L & 4L^2 \end{pmatrix},$$

the conjugate end forces and moments $(EI\,y'''(0),-EI\,y''(0),-EI\,y'''(L),EI\,y''(L))$ equal $K_e d$, and the curvature energy is
$\frac12\int_0^L EI\,(y'')^2\,dx = \frac12 d^{\mathsf T} K_e d$. Axial and bending degrees of freedom are separate; shear deformation, hinge
releases and geometric stiffness are outside this result.

## Depends on

## Proof depends on

## Sources

- University of Manitoba, *ME 478 Finite Element Method*, Chapter 4, *Beam Elements* (the title printed on the PDF): Hermite shape functions, element stiffness matrix and internal strain energy, University of Manitoba, <https://home.cc.umanitoba.ca/~labossip/4510/notes/ch4.pdf>.
