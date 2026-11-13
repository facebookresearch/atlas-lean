# BFS reports exactly the shortest walk length

For every finite directed graph $G$ with
ordered adjacency lists, all vertices $s$ and $v$, and every natural number $d$, breadth-first
search from $s$ reports distance $d$ for $v$ if and only if there is a walk of exactly $d$ edges
from $s$ to $v$ in $G$ and $d \le k$ for every natural number $k$ such that there is a walk of
exactly $k$ edges from $s$ to $v$.
