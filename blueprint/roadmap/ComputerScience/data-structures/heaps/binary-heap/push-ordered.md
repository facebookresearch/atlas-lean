# Insertion into a binary min-heap preserves heap order

For every binary min-heap $h$
over a linearly ordered type and every value $x$, the level-order array of the heap obtained
by inserting $x$ into $h$ is heap-ordered: the entry at every nonroot index $i$ is at least
the entry at its parent index $\lfloor (i-1)/2 \rfloor$.
