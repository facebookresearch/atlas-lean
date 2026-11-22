# Resolution derivability

Given a CNF formula $\varphi$, the clauses derivable from
$\varphi$ by resolution form the smallest set $S$ of clauses that contains every clause of
$\varphi$ and, for every variable $x$ and all clauses $C, D \in S$ such that $C$ contains the
literal $(x, \mathrm{true})$ and $D$ contains the literal $(x, \mathrm{false})$, contains the
resolvent of $C$ and $D$ on $x$.
