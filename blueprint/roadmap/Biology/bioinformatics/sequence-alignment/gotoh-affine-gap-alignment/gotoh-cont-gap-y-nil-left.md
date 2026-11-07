# Continuation after a gap in the first sequence, empty first sequence

Fix a scoring
function $\sigma$ on pairs of letters and integer gap-open and gap-extend penalties $g_o$ and
$g_e$, and let $Y(u, v)$ be the Gotoh continuation value of sequences $u$, $v$ when the previous
column was a gap in $u$. For every sequence $v$ of length $k$, the value $Y(\varepsilon, v)$,
where $\varepsilon$ is the empty sequence, equals $k \, g_e$: the open gap run is extended by
$k$ columns.
