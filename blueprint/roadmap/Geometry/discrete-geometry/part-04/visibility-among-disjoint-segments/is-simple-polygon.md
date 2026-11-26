# Simple polygons

Points $v_0, \dots, v_{n-1} \in \mathbb{R}^2$ form a simple polygon when $n \ge 3$, $v_i \ne v_{i+1}$ for every $i$, and for all indices $i \ne j$ (taken mod $n$), with edges $E_i = [v_i, v_{i+1}]$:

- if $j = i + 1$, then $E_i \cap E_j = \{v_j\}$;
- if $i = j + 1$, then $E_i \cap E_j = \{v_i\}$;
- otherwise $E_i \cap E_j = \emptyset$.
