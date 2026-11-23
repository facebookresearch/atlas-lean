# Positions of the totalized fragment game

A position of the totalized fragment game, over
a type of atoms and a type of worlds, is either an embedded position $(\varphi, w)$ of a
fixpoint-free formula $\varphi$ and a world $w$, standing for the model-checking game position
$(\varphi, w, [])$ with $\varphi$ embedded as a μ-calculus formula and the empty fixpoint stack,
or one of two absorbing states: the winning state, where Verifier has won, and the losing state,
where Refuter has won.

Since the arena contains no fixpoint positions and every move between embedded positions
strictly decreases the formula, priority $0$ on embedded positions is sound. An embedded
position with no moves leads to the winning state if it is a terminal win for Verifier and to
the losing state otherwise, and both absorbing states loop to themselves, so the game has no
dead ends and is a parity game.
