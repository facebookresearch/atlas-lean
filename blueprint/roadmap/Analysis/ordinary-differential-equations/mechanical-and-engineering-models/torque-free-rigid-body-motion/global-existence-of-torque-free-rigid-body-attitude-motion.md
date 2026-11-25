# Global existence of torque-free rigid-body attitude motion

This node covers the torque-free attitude initial-value problem. Let $I$ be a symmetric positive-definite $3 \times 3$ inertia matrix.
For every $\omega_0 \in \mathbb{R}^3$ and $R_0 \in SO(3)$ the system

$$I\dot\omega + \omega \times (I\omega) = 0, \qquad \dot R = R\,[\omega]_\times, \qquad \omega(0) = \omega_0, \ R(0) = R_0,$$

where $[\omega]_\times$ is the skew matrix of $\omega$, has a unique solution defined for all $t \in \mathbb{R}$. Along it the kinetic energy
$\tfrac12\omega\cdot I\omega$ and $|I\omega|$ are constant, the inertial angular momentum $R\,I\omega$ is constant, and $R(t) \in SO(3)$ for all $t$.

## Depends on

- [Exit from compact sets of maximal solutions](../../maximal-solutions-and-global-existence/ode-maximal-solution-exit-compact.md)

## Expansion

A good expansion proves local existence and uniqueness, uses the conserved kinetic energy to confine $\omega$ to a compact set so that
the maximal solution is global, and proves $R^{\mathsf T}R = I$ and $\det R = 1$ by differentiating. Torque inputs, actuator couplings and
quaternion attitude kinematics are separate nodes.

## Sources

- D. T. Greenwood, *Principles of Dynamics*, 2nd edition, Prentice-Hall, 1988, for Euler's equations of rigid-body motion.
