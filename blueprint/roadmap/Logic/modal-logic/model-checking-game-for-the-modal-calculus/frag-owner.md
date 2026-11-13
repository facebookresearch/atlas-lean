# Owners in the totalized fragment game

In the totalized fragment game, an embedded
position $(\varphi, w)$ of a fixpoint-free formula $\varphi$ at a world $w$ is owned by the even
player if Verifier owns the model-checking game position $(\varphi, w, [])$ (with $\varphi$
embedded as a μ-calculus formula and the empty fixpoint stack), and by the odd player otherwise,
that is, when Refuter owns it. The absorbing winning and losing states are both owned by the
even player.

Verifier plays the even player; the moves at the absorbing states are forced, so their owner
does not matter.
