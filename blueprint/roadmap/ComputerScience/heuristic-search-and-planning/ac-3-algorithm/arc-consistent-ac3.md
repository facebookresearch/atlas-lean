# AC-3 makes every arc consistent

Let $P$ be a binary CSP with finitely many variables whose constraints are
[symmetric](symmetric.md) (the arc $(x, y)$ allows $(a, b)$ exactly when the arc $(y, x)$ allows
$(b, a)$) and whose arcs all join two distinct variables, and let $\mathrm{dom}$ be domains for its
variables. Then every arc of $P$ is [consistent](arc-consistent.md) with respect to the domains
returned by [AC-3 on the whole problem](ac3-all.md), run from $\mathrm{dom}$ with every arc of $P$
queued.
