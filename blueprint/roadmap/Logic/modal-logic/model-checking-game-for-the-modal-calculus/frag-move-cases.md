# Moves of the totalized fragment game, by cases

Let $M$ be a Kripke model and $e$ an
environment, and read each fixpoint-free formula $\varphi$ as a μ-calculus formula. Every move
from $a$ to $b$ in the totalized fragment game of $M$ and $e$ is of one of five kinds: $a$ and $b$
are embedded positions $(\varphi, w)$ and $(\varphi', w')$ and the model-checking game of $M$ has a
move from $(\varphi, w)$ to $(\varphi', w')$ with empty binder stacks; or $a = (\varphi, w)$, $b$ is
the winning state, and the game position $(\varphi, w)$ with empty stack has no moves and is won by
Verifier in environment $e$; or $a = (\varphi, w)$, $b$ is the losing state, and that game position
has no moves and is not won by Verifier; or $a$ and $b$ are both the winning state; or $a$ and $b$
are both the losing state.
