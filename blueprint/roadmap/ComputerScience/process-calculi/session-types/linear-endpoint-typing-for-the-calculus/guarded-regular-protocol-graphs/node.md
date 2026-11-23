# Node of a guarded protocol graph

Let $m$ be a natural number and $[m] = \{0, \dots, m-1\}$. A node over $[m]$ is one of:
$\mathrm{end}$; a name send ${!\mathrm{N}}.j$ or a name receive ${?\mathrm{N}}.j$ with successor $j
\in [m]$; or an endpoint send ${!(r,k,t,b)}.j$ or an endpoint receive ${?(r,k,t,b)}.j$ with a
polarity $r$, a rank $k \in \mathbb{N}$, a payload node $t \in [m]$, a Boolean $b$ (whether the
payload protocol is read in reversed orientation) and a successor $j \in [m]$.
