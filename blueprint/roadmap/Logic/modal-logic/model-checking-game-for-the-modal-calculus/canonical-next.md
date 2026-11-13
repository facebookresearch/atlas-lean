# Canonical next move induced by a bespoke strategy

Let $M$ be a Kripke model,
$\mathit{env}$ an environment and $\sigma$ a Verifier strategy for the model-checking game on
$M$. Write $\langle \psi, v \rangle$ for the game position with the embedding of a
fixpoint-free formula $\psi$, the world $v$ and the empty binder stack. The canonical next move
is the map on positions of the fragment arena defined as follows. The absorbing states
$\mathrm{win}$ and $\mathrm{lose}$ are sent to themselves. A fragment position $(\varphi, w)$
such that $\langle \varphi, w \rangle$ has a move to some $\langle \varphi', w' \rangle$ is
sent, if Verifier owns $\langle \varphi, w \rangle$, to the projection into the fragment arena
of the position that $\sigma$ chooses there (an embedded position $\langle \varphi', w' \rangle$
projects to $(\varphi', w')$, every other game position to $\mathrm{lose}$), and otherwise to a
fragment position $(\varphi', w')$ chosen, by the axiom of choice, among those with a move from
$\langle \varphi, w \rangle$ to $\langle \varphi', w' \rangle$. A fragment position
$(\varphi, w)$ with no such move is sent to $\mathrm{win}$ if $\langle \varphi, w \rangle$
satisfies the terminal winning condition for Verifier in environment $\mathit{env}$, and to
$\mathrm{lose}$ otherwise.
