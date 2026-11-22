# Triangle inequality for the coded distance

For continuous $g$, $d_g(s, u) \le d_g(s, t) + d_g(t, u)$. Equivalently,
$m_g(s, t) + m_g(t, u) \le g(t) + m_g(s, u)$, which holds because the larger of the two minima is
at most $g(t)$ and the smaller is at most $m_g(s, u)$, as the interval between $s$ and $u$ lies in
the union of the intervals between $s$ and $t$ and between $t$ and $u$.

## Informally uses

- [Ultrametric inequality for the minimum](min-tree-min-le.md): the smaller of $m_g(s, t)$ and
  $m_g(t, u)$ is at most $m_g(s, u)$.
