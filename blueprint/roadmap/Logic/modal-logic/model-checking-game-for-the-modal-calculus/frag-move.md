# Moves of the totalized fragment game

Let $M$ be a Kripke model and $e$ an environment,
and read each fixpoint-free formula $\varphi$ as a μ-calculus formula. The totalized fragment game
of $M$ and $e$ has these moves: from an embedded position $(\varphi, w)$ to $(\varphi', w')$
whenever the model-checking game of $M$ has a move from $(\varphi, w)$ to $(\varphi', w')$ with
empty binder stacks; from $(\varphi, w)$ to the winning state when the game position
$(\varphi, w)$ with empty stack has no moves and is won by Verifier in environment $e$; from
$(\varphi, w)$ to the losing state when that game position has no moves and is not won by
Verifier; and from each of the winning and losing states to itself.
