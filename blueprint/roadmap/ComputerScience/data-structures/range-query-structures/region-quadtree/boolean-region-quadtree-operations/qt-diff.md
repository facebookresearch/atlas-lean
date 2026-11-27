# Difference of Boolean quadtrees

The difference $s \setminus t$ of two Boolean region quadtrees (cells in the first region and not
in the second) is defined recursively.

- If $s = L(\mathrm{false})$, then $s \setminus t = L(\mathrm{false})$; if $s = L(\mathrm{true})$,
  then $s \setminus t$ is the complement of $t$.
- If $s$ is a branch and $t = L(\mathrm{false})$, then $s \setminus t = s$; if $s$ is a branch and
  $t = L(\mathrm{true})$, then $s \setminus t = L(\mathrm{false})$.
- If $s = Q(s_0, s_1, s_2, s_3)$ and $t = Q(t_0, t_1, t_2, t_3)$, then $s \setminus t$ is the
  compressing branch constructor applied to $s_0 \setminus t_0$, $s_1 \setminus t_1$,
  $s_2 \setminus t_2$, $s_3 \setminus t_3$.
