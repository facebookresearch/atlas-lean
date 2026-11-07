# No infinite play from a fragment position

Let $M$ be a Kripke model, $\varphi$ a
fixpoint-free formula and $w$ a world. There is no sequence of game positions
$p_0, p_1, p_2, \dots$ with $p_0 = (\varphi, w, [\,])$ (the embedded formula with the empty
stack) such that each step from $p_n$ to $p_{n+1}$ is a move of the model-checking game in $M$.
The reason is that every move strictly decreases the formula size.
