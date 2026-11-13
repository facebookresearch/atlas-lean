# Separating conjunction

For heap assertions $P$ and $Q$, the assertion $P \star Q$ holds
of a store $s$ and a heap $h$ when there are disjoint heaps $h_1$ and $h_2$ with
$h = h_1 \cup h_2$ such that $P(s, h_1)$ and $Q(s, h_2)$.
