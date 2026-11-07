# Cascade of projections as a query rewrite

Fix a database schema $\mathrm{sch}$
assigning a finite set of attributes to each base relation name. Let $e$ be a well-formed query
with schema $S$, and let $T \subseteq T' \subseteq S$ be finite sets of attributes. Then the
query $\pi_T(\pi_{T'}(e))$, the projection onto $T$ of the projection of $e$ onto $T'$, is
equivalent to the query $\pi_T(e)$, the projection of $e$ onto $T$: both are well-formed with
the same schema, and they have equal values on every database conforming to $\mathrm{sch}$.
