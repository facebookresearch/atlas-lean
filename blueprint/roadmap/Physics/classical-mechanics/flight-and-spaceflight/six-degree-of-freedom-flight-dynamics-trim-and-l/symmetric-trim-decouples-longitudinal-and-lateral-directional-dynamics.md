# Symmetric trim decouples longitudinal and lateral-directional dynamics

Consider a rigid aircraft whose mass distribution and aerodynamic force and moment maps are invariant under reflection in its body $xz$-plane, the plane of symmetry. Use body axes with $x$ and $z$ in that plane. Linearize the [six-degree-of-freedom body equations](six-dof-body-equations.md) about a trimmed flight condition that is itself symmetric, meaning zero sideslip, roll rate, yaw rate and bank angle, with symmetric control settings.

Split the perturbation state and controls into:
- *longitudinal*: $u, w, q, \theta$, with elevator and throttle;
- *lateral-directional*: $v, p, r, \phi$, with aileron and rudder.

**Theorem.** In the linearized equations $\dot x = Ax + Bu$, the matrices $A$ and $B$ are block diagonal with respect to this split. The longitudinal forces and pitching moment ($X$, $Z$, $M$) do not depend on lateral-directional perturbations or controls. The side force, rolling moment and yawing moment ($Y$, $L$, $N$) do not depend on longitudinal perturbations or controls. In particular the products of inertia satisfy $I_{xy} = I_{yz} = 0$, while $I_{xz}$ may be nonzero and couples only roll and yaw.

**Proof.** Reflection in the symmetry plane maps a motion to a motion. In body components it acts by a linear involution $S$ that fixes every longitudinal variable and longitudinal control, and negates every lateral-directional variable and control: $v, p, r, \phi$ and the aileron and rudder deflections change sign. The equations of motion are equivariant under $S$, and the trim point is fixed by $S$. Hence the Jacobians at the trim commute with $S$: $SA = AS$ and $SB = BS$. A linear map that commutes with an involution preserves its $\pm 1$ eigenspaces, so $A$ and $B$ map longitudinal to longitudinal and lateral to lateral. Invariance of the mass distribution under $y \mapsto -y$ gives $I_{xy} = I_{yz} = 0$.

The decoupling is exact only to first order. For example, the lift change from a roll rate cancels between the two wings only in the linear approximation. Analyzing a particular aircraft also needs published stability and control derivatives with their validity domains, a trim-existence argument, and analysis of the lateral modes (spiral, roll subsidence and Dutch roll).

## Depends on

- [Six-degree-of-freedom body equations of a rigid motion](six-dof-body-equations.md)

## Background

- [The trim is a relative equilibrium](trim-relative-equilibrium.md)
- [The trim Jacobian is block diagonal](longitudinal-jacobian-eq-from-blocks.md)

## Sources

- *Dynamical Equations for Flight Vehicles*, Chapter 4 of the course notes for MAE 5070, Cornell University, <https://courses.cit.cornell.edu/mae5070/DynamicEquations.pdf>:
    - Section 4.1: body axes in the symmetry plane, and $I_{xy} = I_{yz} = 0$ by vehicle symmetry;
    - Section 4.2: the linearized force and moment equations (4.25)–(4.26);
    - Section 4.3: the decoupled longitudinal and lateral-directional aerodynamic dependencies (4.27)–(4.28), exact for the lateral forces and moments and correct to first order for the converse.
- J. How, *16.61 Aerospace Dynamics*, Lecture AC-3 "Aircraft lateral dynamics: spiral, roll, and Dutch roll modes", MIT OpenCourseWare, 2003, <https://ocw.mit.edu/courses/16-61-aerospace-dynamics-spring-2003/1f0a14b69fb824f3892ddb008b037b80_lecture18.pdf>: the lateral state $(v, p, r, \phi)$ with its $A$ and $B$ matrices, and the spiral, roll and Dutch roll modes.
