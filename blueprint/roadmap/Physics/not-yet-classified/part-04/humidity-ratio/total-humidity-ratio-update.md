# Total humidity ratio update

Let a finite network of nodes and arcs carry water masses $m_v$ at the nodes, with arc flows $F$, external additions $s_v$ and retirements $r_v$, and let the updated masses be $m' = m + B F + s - r$, where $B$ is the node-arc incidence matrix ($B_{ve} = 1$ if arc $e$ ends at $v$, $-1$ if it starts at $v$). For a constant dry-air mass $m_{da} > 0$, the total humidity ratio satisfies

$$\frac{\sum_v m'_v}{m_{da}} = \frac{\sum_v m_v}{m_{da}} + \frac{\sum_v s_v - \sum_v r_v}{m_{da}}.$$
