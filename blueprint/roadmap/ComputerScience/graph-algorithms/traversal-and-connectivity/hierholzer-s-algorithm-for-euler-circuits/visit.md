# Hierholzer's recursion

Given a fuel $n$, a vertex $v$, an assignment $R$ of a list of
remaining out-neighbours to each vertex, and a list $\mathit{acc}$ of vertices, the recursion
returns a list of vertices and a new assignment, with a cost. With fuel $0$ it returns
$(\mathit{acc}, R)$ at cost $0$. With fuel $n + 1$: if $R(v)$ is empty, it returns $v$ followed by
$\mathit{acc}$ together with $R$, at cost $0$; otherwise $R(v)$ is $w$ followed by a list
$\mathit{rest}$, and it replaces $R(v)$ by $\mathit{rest}$, runs the recursion with fuel $n$ from
$w$ on the new assignment with accumulator $\mathit{acc}$, obtaining $(L_1, R_1)$, and returns the
result of the recursion with fuel $n$ from $v$ on $R_1$ with accumulator $L_1$, at cost $1$ plus
the costs of the two calls.

This follows unused edges depth first and splices sub-tours in; too little fuel can stop it
early. Hierholzer's algorithm runs it with fuel one more than the number of edge occurrences.
