# The canonical move follows the bespoke strategy at Verifier positions with a move

Let
$M$ be a Kripke model, $\mathit{env}$ an environment and $\sigma$ a Verifier strategy for the
model-checking game on $M$. Write $\langle \psi, v \rangle$ for the game position with the
embedding of a fixpoint-free formula $\psi$, the world $v$ and the empty binder stack. Let
$\varphi$ be a fixpoint-free formula and $w$ a world such that Verifier owns
$\langle \varphi, w \rangle$ and $\langle \varphi, w \rangle$ has a move to some
$\langle \varphi'', w'' \rangle$. Then there are a fixpoint-free formula $\varphi'$ and a world
$w'$ such that the canonical next move induced by $\sigma$ (in environment $\mathit{env}$) sends
the fragment position $(\varphi, w)$ to the fragment position $(\varphi', w')$, and $\sigma$
chooses $\langle \varphi', w' \rangle$ at $\langle \varphi, w \rangle$.
