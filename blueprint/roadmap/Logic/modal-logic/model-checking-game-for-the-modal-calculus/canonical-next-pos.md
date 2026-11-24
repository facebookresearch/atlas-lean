# Verifier's positional strategies make a game move at Verifier positions that have one

Let $M$ be a Kripke model, $\mathit{env}$ an environment, and $\sigma$ any positional strategy of
the even player (Verifier) in the fragment game of $M$ and $\mathit{env}$. Write
$\langle \psi, v \rangle$ for the game position with the embedding of a fixpoint-free formula
$\psi$, the world $v$ and the empty binder stack. Let $\varphi$ be a fixpoint-free formula and
$w$ a world such that the even player owns the fragment position $(\varphi, w)$ and, in the
model-checking game on $M$, $\langle \varphi, w \rangle$ has a move to some
$\langle \varphi'', w'' \rangle$. Then $\sigma$ sends $(\varphi, w)$ to a fragment position
$(\varphi', w')$ such that $\langle \varphi, w \rangle$ has a move to
$\langle \varphi', w' \rangle$; in particular $\sigma$ does not move to the absorbing state
$\mathrm{win}$ or $\mathrm{lose}$.
