# Continuation after a gap in the second sequence, empty second sequence

Fix a scoring
function $\sigma$ on pairs of letters and integer gap-open and gap-extend penalties $g_o$ and
$g_e$, and let $X(u, v)$ be the Gotoh continuation value of sequences $u$, $v$ when the previous
column was a gap in $v$. For every sequence $u$ of length $k$, the value $X(u, \varepsilon)$,
where $\varepsilon$ is the empty sequence, equals $k \, g_e$: the open gap run is extended by
$k$ columns.
