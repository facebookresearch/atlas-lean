# Continuation after a gap in the second sequence, empty first sequence

Fix a scoring
function $\sigma$ on pairs of letters and integer gap-open and gap-extend penalties $g_o$ and
$g_e$, and let $X(u, v)$ be the Gotoh continuation value of sequences $u$, $v$ when the previous
column was a gap in $v$. For every sequence $v$ of length $k$, the value $X(\varepsilon, v)$,
where $\varepsilon$ is the empty sequence, is the cost of one freshly opened gap run of length
$k$: it is $0$ if $k = 0$ and $g_o + (k - 1) g_e$ if $k \ge 1$.
