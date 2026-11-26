# Terminal losing positions are not won by the even player

Let $M$ be a Kripke model,
$\mathit{env}$ an environment assigning a set of worlds to each free-variable index, $\varphi$ a
fixpoint-free formula and $w$ a world. If the model-checking game position $(\varphi, w, [])$,
with $\varphi$ embedded as a μ-calculus formula and the empty fixpoint stack, has no moves in $M$
and is not a terminal win for Verifier in $M$ under $\mathit{env}$, then the embedded position
$(\varphi, w)$ of the totalized fragment game of $M$ and $\mathit{env}$ is not in the winning
region of the even player.

The play that moves from $(\varphi, w)$ to the losing state and stays there conforms to every
strategy of the even player and is won by the odd player.
