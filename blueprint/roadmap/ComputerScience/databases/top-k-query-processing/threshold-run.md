# Run of the threshold algorithm

For graded sorted lists, an aggregation function $t$ and
$k \in \mathbb{N}$, a run of the threshold algorithm is a sequence of buffers $B_0, B_1, \ldots$
of objects, $B_d$ being the buffer after $d$ rounds of sorted access in parallel. The buffer
$B_0$ is empty, and round $d + 1$ reads the objects at position $d$ of the lists, finds their
aggregate grades by random access, and keeps as $B_{d+1}$ a top-$k$ choice for the aggregate
grade among $B_d$ and the objects just read: $k$ of them of highest aggregate grade, or all of
them if there are fewer than $k$. Ties are resolved arbitrarily, so each choice of ties gives a
run.
