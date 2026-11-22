# Query equivalence

Let $\mathrm{sch}$ be a database schema, assigning a finite set of
attributes to each relation name. Two queries $e$ and $e'$ are equivalent with respect to
$\mathrm{sch}$ when there is a finite set of attributes $S$ such that the inferred schemas of
$e$ and of $e'$ with respect to $\mathrm{sch}$ are both $S$ (in particular both queries are
well-formed), and $e$ and $e'$ evaluate to the same relation on every database that conforms
to $\mathrm{sch}$.
