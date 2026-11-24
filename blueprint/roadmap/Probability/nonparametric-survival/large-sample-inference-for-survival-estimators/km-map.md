# Kaplan–Meier map on cell space

The Kaplan–Meier map at grid index $m$ sends a cell vector $v$ to $\prod_{j\le m}\big(1 - v(j, 1)/\sum_{l\ge j}(v(l, 1) + v(l, 0))\big)$, where a factor with zero at-risk mass $\sum_{l\ge j}(v(l, 1) + v(l, 0)) = 0$ equals $1$ ($x/0 = 0$).
