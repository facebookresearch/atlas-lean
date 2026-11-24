# Derivative of the Kaplan–Meier map

At a cell vector $p$ with $e_j = p(j, 1)$, at-risk masses $Y_j$ and at-risk functionals $A_j$, the derivative of the Kaplan–Meier map at $m$ is $v \mapsto \sum_{j\le m}\prod_{l\le m, l\ne j}(1 - e_l/Y_l)\cdot(e_jA_j(v) - Y_jv(j, 1))/Y_j^2$, with $x/0 = 0$: a term with $Y_j = 0$ is $0$ and a factor with $Y_l = 0$ is $1$.
