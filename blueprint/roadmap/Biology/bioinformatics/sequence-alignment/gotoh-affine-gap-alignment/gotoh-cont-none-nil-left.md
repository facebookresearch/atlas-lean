# Gotoh value against an empty first sequence

Let $g_o$ and $g_e$ be the gap-open and
gap-extend scores. For every sequence $y$ of length $n$, the Gotoh value with no open gap run of
the empty sequence against $y$ equals the score of a freshly opened run of $n$ gaps in the first
sequence: $0$ if $n = 0$, and $g_o + (n - 1) g_e$ if $n \ge 1$.
