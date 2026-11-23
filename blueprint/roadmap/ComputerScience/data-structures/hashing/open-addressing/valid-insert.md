# Insertion preserves validity of an open-addressing table

Let $T$ be a valid table with $m$
slots and probe sequence $p$, whose keys have decidable equality. If inserting the binding
$k \mapsto v$ into $T$ (adding it, or replacing the binding already stored for $k$) succeeds and
returns the table $T'$, then $T'$ is valid: it is probe-closed and no key is stored in two
different slots.
