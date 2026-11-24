# Steady-state core-conductor equations on a set of positions

For real numbers $r_m$ and $r_i$, a set $S\subseteq\mathbb R$ of positions and real functions $V$
and $I$, the pair $(V,I)$ is a steady state of the passive cable on $S$ if at every $x\in S$

- $V$ has derivative $-r_i I(x)$ within $S$ at $x$ (Ohm's law along the core), and
- $I$ has derivative $-V(x)/r_m$ within $S$ at $x$ (the axial current decreases by the passive
  membrane current).

Here $V$ is the membrane voltage measured from rest and $I$ the axial current in the direction of
increasing $x$. Derivatives are taken within $S$, so they are one-sided at the ends of an interval,
and at an isolated point of $S$ the conditions are always satisfied. With the convention $u/0=0$,
the second equation reads $I'=0$ when $r_m=0$. In the model $r_m$ and $r_i$ are positive.
