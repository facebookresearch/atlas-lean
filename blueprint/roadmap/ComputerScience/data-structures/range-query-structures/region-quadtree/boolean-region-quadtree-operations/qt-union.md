# Union of Boolean quadtrees

The union $s \cup t$ of two Boolean region quadtrees is defined recursively.

- If $s = L(\mathrm{true})$, then $s \cup t = L(\mathrm{true})$; if $s = L(\mathrm{false})$, then
  $s \cup t = t$.
- If $s$ is a branch and $t = L(\mathrm{true})$, then $s \cup t = L(\mathrm{true})$; if $s$ is a
  branch and $t = L(\mathrm{false})$, then $s \cup t = s$.
- If $s = Q(s_0, s_1, s_2, s_3)$ and $t = Q(t_0, t_1, t_2, t_3)$, then $s \cup t$ is the
  compressing branch constructor applied to $s_0 \cup t_0$, $s_1 \cup t_1$, $s_2 \cup t_2$,
  $s_3 \cup t_3$.
