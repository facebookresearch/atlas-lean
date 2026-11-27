# Time-triggered controllers as hybrid automata

Let a sampled-data loop have a plant flow $\phi$ with no disturbance, a controller with state update $z' = g(z, y)$ and
output $\kappa(z, y)$ applied every $h > 0$ time units to the observation $y$ of the plant state, and zero-order hold. Model it
as a hybrid automaton with a clock $c$ ($\dot c = 1$, invariant $c \le h$) whose single jump, at $c = h$, reads the observation
$y$ of the current plant state $x$ and sets, simultaneously, the held control $u := \kappa(z, y)$, the controller state
$z := g(z, y)$ and $c := 0$. Start it at $c = 0$ from the state obtained by applying the same update to the initial plant and
controller states $(x_0, z_0)$. The plant state lies in $\mathbb{R}^n$, and the controller state and the held control are real
vectors that stay constant during flows. Assume the flow exists on $[0, h]$ from every state considered and consider maximal
executions in which time progresses (no execution stops before the next jump). Then $(x_0, z_0)$ followed by the plant and
controller states just before the jumps at times $h, 2h, \dots$ is the trajectory of the discrete closed loop formed by
$f_h(x, u) = \phi_h(x, u)$ and the controller, and every execution is non-Zeno with dwell time $h$. Safety between samples is a
separate condition on the flow segments.

## Proof

Write $(x_k, z_k)$ for the discrete closed-loop trajectory, $y_k$ for the observation of $x_k$ and $u_k = \kappa(z_k, y_k)$, so
that $x_{k+1} = f_h(x_k, u_k)$ and $z_{k+1} = g(z_k, y_k)$. Suppose that at time $kh$, just after the update, the automaton holds
$(x_k, z_{k+1}, u_k)$ with $c = 0$; for $k = 0$ this is the initial state. During $[kh, (k+1)h]$ the clock rises from $0$ to $h$,
$z_{k+1}$ and $u_k$ stay constant, and the plant follows $\phi$ from $x_k$ under $u_k$, so it reaches $\phi_h(x_k, u_k) = x_{k+1}$. The
invariant $c \le h$ forbids flowing past $(k+1)h$, and the guard allows the jump only there, so every maximal time-progressing
execution jumps exactly at $(k+1)h$, from the state with plant and controller components $(x_{k+1}, z_{k+1})$, and the update
gives $(x_{k+1}, z_{k+2}, u_{k+1})$. Induction gives the claim. Consecutive jumps are $h$ apart, so finitely many jumps occur in
any bounded time.

## Depends on

- [Zeno executions and finite-jump hypotheses](remaining-clauses-of-zeno-executions-and-finite-jump-hypothe.md)
- [Hybrid automata and their executions](hybrid-automata-and-their-executions.md)
- [Closed-loop composition of plant and controller as discrete dynamics](../discrete-time-systems-and-safety/closed-loop-composition-of-plant-and-controller-as-discrete.md)
- [Sampling a continuous-time flow into discrete dynamics](../discrete-time-systems-and-safety/sampling-a-continuous-time-flow-into-discrete-dynamics.md)

## Sources

- E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., Springer, 1998,
  Section 2.10, Definition 2.10.1 (p. 72): the sampled system $f_h$. The agreement at sample times is derived above.
  <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>
