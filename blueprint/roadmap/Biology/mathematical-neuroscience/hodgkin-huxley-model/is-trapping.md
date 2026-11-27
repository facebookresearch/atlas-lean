# Trapping voltage interval

For a [parameter set](params.md), real numbers $V_{lo}$ and $V_{hi}$ form a trapping interval
$[V_{lo}, V_{hi}]$ if

- $V_{lo} \le E_{Na}$, $V_{lo} \le E_K$ and $g_L\,(V_{lo} - E_L) < I$;
- $E_{Na} \le V_{hi}$, $E_K \le V_{hi}$ and $I < g_L\,(V_{hi} - E_L)$.

For [valid parameters](valid.md), [solutions starting in the box](mem-box.md)
$[V_{lo}, V_{hi}] \times [0, 1]^3$ stay in it.
