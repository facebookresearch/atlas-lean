# Winning strategy from a position

Let $M$ be a Kripke model, $\mathit{env}$ an environment
assigning a predicate on worlds to every index, $\sigma$ a Verifier strategy for the
model-checking game on $M$ and $p$ a game position. A play is consistent with $\sigma$ when each
step is a move and, at every Verifier-owned position, goes to the position chosen by $\sigma$.
The strategy $\sigma$ wins from $p$ in $\mathit{env}$ when every finite play from $p$ consistent
with $\sigma$ whose last position has no moves ends in a position that is a terminal win for
Verifier in $\mathit{env}$, and every infinite play from $p$ consistent with $\sigma$ satisfies
the parity condition.
