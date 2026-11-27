# Bound on the number of AC-3 revisions

For a binary CSP $P$ with finitely many variables
and initial domains $\mathrm{dom}$, AC-3 run from $\mathrm{dom}$ with every arc of $P$ queued
performs at most $m + \sum_x |\mathrm{dom}(x)| \cdot \mathrm{indeg}(x)$ revisions, where $m$ is
the length of the arc list of $P$ and $\mathrm{indeg}(x)$ is the number of entries of that list
ending at $x$.

This is $O(e d)$ for $e$ arcs and domains of size $d$.
