# Lists of equations with the same unifiers satisfy the same specification

Let $E$ and
$E'$ be lists of equations such that a substitution unifies $E$ exactly when it unifies $E'$.
If an optional substitution $r$ satisfies the unification specification for $E'$ (a returned
substitution $s$ unifies the list and every unifier $s'$ of it satisfies $s' = s \gg s'$,
where $s \gg s'$ applies first $s$ and then $s'$, and failure means the list has no unifier),
then $r$ satisfies the unification specification for $E$.
