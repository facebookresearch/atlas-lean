# Schema of a query

Given a database schema assigning a finite set $\mathrm{sch}(n)$ of
attributes to each base relation name $n$, the schema of a relational algebra query is either a
finite set of attributes or undefined (the query is ill-formed), defined by recursion on the
query: the base relation $n$ has schema $\mathrm{sch}(n)$; if $e$ has schema $S$, then the
selection $\sigma_c(e)$ has schema $S$ when every attribute of the condition $c$ lies in $S$, the
projection $\pi_T(e)$ has schema $T$ when $T \subseteq S$, and the renaming $\rho_f(e)$ along a
permutation $f$ of the attributes has schema $f(S)$; if $e$ and $e'$ have schemas $S$ and $S'$,
then the natural join of $e$ and $e'$ has schema $S \cup S'$, and their union and their
difference have schema $S$ when $S = S'$. In every other case, including when an operand is
ill-formed, the schema is undefined.
