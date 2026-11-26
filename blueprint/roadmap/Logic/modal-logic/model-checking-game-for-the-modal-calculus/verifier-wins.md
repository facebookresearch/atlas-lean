# Verifier has a winning strategy

For a Kripke model $M$, an environment $\mathit{env}$
and a game position $p$, Verifier wins from $p$ when some Verifier strategy $\sigma$ in the
model-checking game on $M$ wins from $p$ in environment $\mathit{env}$: every complete finite
$\sigma$-consistent play from $p$ ends at a terminal winning position, and every infinite
$\sigma$-consistent play from $p$ satisfies the parity condition.
