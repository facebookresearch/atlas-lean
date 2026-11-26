# Arc consistency invariant of AC-3

Let $P$ be a binary CSP with finitely many variables
whose constraints are symmetric, that is the arc $(x, y)$ allows $(a, b)$ exactly when the arc
$(y, x)$ allows $(b, a)$, and whose arcs all join two distinct variables. Let $\mathrm{dom}$ be
domains and $q$ a queue whose entries are arcs of $P$, such that every arc of $P$ not in $q$ is
consistent with respect to $\mathrm{dom}$. Then every arc of $P$ is consistent with respect to the
domains returned by AC-3 run from $\mathrm{dom}$ with queue $q$.

The invariant: every arc of the problem outside the queue stays consistent, and at the end the
queue is empty.
