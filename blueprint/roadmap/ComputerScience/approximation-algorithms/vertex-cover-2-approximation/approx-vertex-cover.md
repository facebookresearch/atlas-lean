# APPROX-VERTEX-COVER

Given a list $L$ of ordered pairs of vertices, APPROX-VERTEX-COVER
starts from the empty cover and goes through $L$ in order: a pair $(u, v)$ with $u$ or $v$ already
in the cover is skipped, and otherwise both $u$ and $v$ are added to the cover. It returns the
final cover, a finite set of vertices, at a cost of one unit per pair of $L$.

CLRS (third edition, Section 35.1) takes an arbitrary uncovered edge at each step; here it is the
first uncovered pair in list order.
