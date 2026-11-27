# Closed-loop composition of plant and controller as discrete dynamics

Let a plant be $(X, U \times W, f)$ with update $x' = f(x, u, w)$ for a control input $u$ and a disturbance $w$, and an
observation map $h : X \to Y$. Let a controller be $(Z, Y, g, \kappa)$ with internal update $z' = g(z, y)$ and output map
$\kappa : Z \times Y \to U$. Since $f$ is total, every control is admissible at every plant state and the closed loop has no
deadlocks; for a plant given instead by a successor relation, the closed loop at $(x, z)$ is defined only when $\kappa(z, h(x))$ is
enabled at $x$, and a state where it is not is a deadlock. The closed loop
is the discrete system on $X \times Z$ with disturbance input $w$:
$(x, z) \mapsto (f(x, \kappa(z, h(x)), w),\ g(z, h(x)))$; at each step the controller reads the current observation, outputs a
control, and both components update simultaneously. The sampled-data variant, which holds the control constant over a
sampling period, is a separate definition.

## Depends on

- [Discrete-time dynamical system (input-driven state-update map)](discrete-time-dynamical-system.md)

## Sources

- E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., Springer, 1998,
  Definition 7.2.3 and Lemma 7.2.4 (pp. 322–323): the interconnection of two systems through connecting maps
  $k_i : Y_1 \times Y_2 \to U_i$. The closed loop above is the discrete-time case with the controller's state as its output,
  $k_1(y, z) = \kappa(z, y)$ and $k_2(y, z) = y$, except that the disturbance $w$ is kept as an external input.
  <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>
