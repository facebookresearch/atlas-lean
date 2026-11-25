# Radiosity matrix is strictly diagonally dominant

A *black enclosure* on a finite set of surfaces $i$ is a pair of areas $A_i$ and view factors $F_{ij}$ with $A_i > 0$, $F_{ij} \ge 0$, $\sum_j F_{ij} = 1$ for every $i$, and reciprocity $A_i F_{ij} = A_j F_{ji}$ for all $i, j$. Let the emissivities satisfy $0 < \varepsilon_i \le 1$ for every $i$, and let $M = I - \operatorname{diag}(1 - \varepsilon) F$ be the radiosity matrix, $M_{ij} = \delta_{ij} - (1 - \varepsilon_i) F_{ij}$. Then for every row $k$,

$$\sum_{j \ne k} |M_{kj}| < |M_{kk}|.$$
