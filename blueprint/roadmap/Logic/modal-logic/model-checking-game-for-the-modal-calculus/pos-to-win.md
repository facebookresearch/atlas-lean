# Moves to the winning state come from terminal winning positions

Let $M$ be a Kripke
model, $\mathrm{env}$ an environment, $\varphi$ a fixpoint-free formula and $w$ a world. If the
totalized fragment game has a move from the embedded position $(\varphi, w)$ to the absorbing
winning state, then the game position $(\varphi, w, [])$, with $\varphi$ viewed as a μ-calculus
formula and an empty binder stack, has no moves, and Verifier wins there as a terminal position
in the environment $\mathrm{env}$.
