# Bisimulation

Let $M$ and $N$ be Kripke models over the same atoms, with sets of
worlds $W$ and $V$ and accessibility relations $R_M$ and $R_N$. A relation
$Z \subseteq W \times V$ is a bisimulation between $M$ and $N$ when, for all $w \in W$ and
$v \in V$ with $w \mathrel{Z} v$: each atom $a$ is true at $w$ in $M$ if and only if $a$ is
true at $v$ in $N$; for every $w'$ with $w \mathrel{R_M} w'$ there is $v'$ with
$v \mathrel{R_N} v'$ and $w' \mathrel{Z} v'$ (forth); and for every $v'$ with
$v \mathrel{R_N} v'$ there is $w'$ with $w \mathrel{R_M} w'$ and $w' \mathrel{Z} v'$ (back).
