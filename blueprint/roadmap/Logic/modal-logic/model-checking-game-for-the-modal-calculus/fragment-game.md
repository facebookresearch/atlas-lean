# Fragment parity game

Let $M$ be a Kripke model and $\rho$ an environment, and write
$(\varphi, w, [])$ for the game position with formula $\varphi$, world $w$ and empty binder
stack. The fragment game of $M$ and $\rho$ is the parity game on the totalized fragment
positions defined as follows. An embedded position $(\varphi, w)$ moves to $(\varphi', w')$
when $(\varphi, w, [])$ has a move to $(\varphi', w', [])$ in the model-checking game on $M$;
if $(\varphi, w, [])$ has no moves, $(\varphi, w)$ moves to the winning state when
$(\varphi, w, [])$ is a terminal win in $\rho$ and to the losing state otherwise; the winning
and losing states move only to themselves. The even player owns both absorbing states and the
embedded positions $(\varphi, w)$ such that Verifier owns $(\varphi, w, [])$; the odd player
owns the other embedded positions. Embedded positions and the winning state have priority $0$;
the losing state has priority $1$.
