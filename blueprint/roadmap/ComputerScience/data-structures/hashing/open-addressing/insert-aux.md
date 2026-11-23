# Bounded insertion scan

Given a table with $m$ slots and probe sequence $p$, a key $k$, a
value $v$, a starting index $s$ and a budget $f$ of probes, examine the slots
$p(k, s), p(k, s + 1), \dots$ in order, for at most $f$ probes. At the first examined slot that
is empty or holds a binding for $k$, the scan returns the table with that slot overwritten by the
binding $k \mapsto v$ and every other slot unchanged; if all $f$ examined slots hold bindings for
other keys (in particular if $f = 0$), it fails and returns no table.

This is the helper behind insertion, which starts at index $0$ with budget $m$.
