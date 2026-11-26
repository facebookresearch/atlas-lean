# Cascade of selections as a query rewrite

Fix a database schema $\mathrm{sch}$
assigning a finite set of attributes to each base relation name. Let $e$ be a well-formed query
with schema $S$, and let $c$ and $c'$ be selection conditions all of whose attributes lie in
$S$. Then the query $\sigma_c(\sigma_{c'}(e))$, the selection by $c$ of the selection of $e$ by
$c'$, is equivalent to the query $\sigma_{c' \land c}(e)$, the selection of $e$ by the
conjunction $c' \land c$: both are well-formed with the same schema, and they have equal values
on every database conforming to $\mathrm{sch}$.
