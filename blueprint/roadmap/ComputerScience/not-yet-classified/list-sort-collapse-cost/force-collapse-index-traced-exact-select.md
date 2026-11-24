# Force Collapse Index Traced exact selector

Exact source selector pin for stacks of depth at least three.

The final three pending runs are exposed as `a,b,c`.  The returned merge index
is the third-last pair exactly when `a.len < c.len` as naturals; ties and the
opposite strict inequality select the top pair.
