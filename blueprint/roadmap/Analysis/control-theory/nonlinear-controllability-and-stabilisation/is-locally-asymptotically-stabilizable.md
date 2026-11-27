# Stabilisability by continuous stationary feedback

The control system $\dot x = f(x, u)$, $f : E \times U \to E$, is **locally asymptotically stabilisable by continuous stationary feedback laws** if there is a continuous $u : E \to U$ with $u(0) = 0$ such that $0$ is locally asymptotically stable for the closed-loop system $\dot x = f(x, u(x))$ (Coron, *Control and Nonlinearity*, AMS 2007, Definition 10.11). "Stationary" distinguishes these feedback laws from the time-varying feedback laws $u(x, t)$ of Coron's Section 11.2.

## Background

- [Local asymptotic stability of an equilibrium of a continuous vector field](is-locally-asymptotically-stable.md): the required property of the closed loop.
