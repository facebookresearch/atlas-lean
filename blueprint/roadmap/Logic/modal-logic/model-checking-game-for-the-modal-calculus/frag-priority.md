# Priorities in the totalized fragment game

In the totalized fragment game, every embedded
position $(\varphi, w)$ of a fixpoint-free formula $\varphi$ at a world $w$ has priority $0$, the
absorbing winning state has priority $0$, and the absorbing losing state has priority $1$.

So an infinite play that eventually stays at the winning state is won by the even player, and
one that eventually stays at the losing state by the odd player. Priority $0$ on embedded
positions is sound because the arena contains no fixpoint positions and every move between
embedded positions strictly decreases the formula, so no infinite play visits only embedded
positions.
