# Selection pushdown as a query rewrite

Fix a database schema $\mathrm{sch}$ assigning a
finite set of attributes to each base relation name. Let $e$ and $e'$ be well-formed queries with
schemas $S$ and $S'$, and let $c$ be a selection condition all of whose attributes lie in $S$.
Then the query $\sigma_c(e \bowtie e')$, the selection by $c$ of the natural join of $e$ and $e'$,
is equivalent to the query $\sigma_c(e) \bowtie e'$: both are well-formed with the same schema,
and they have equal values on every database conforming to $\mathrm{sch}$.
