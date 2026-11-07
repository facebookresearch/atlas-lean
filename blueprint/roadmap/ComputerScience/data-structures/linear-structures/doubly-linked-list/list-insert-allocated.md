# Doubly-linked-list insertion neither allocates nor frees cells

For a store $S$ and
allocated cells $x$ and $y$ such that the successor of $y$ in $S$, if any, is allocated, every
cell $z$ of the store returned by inserting $x$ after $y$ is allocated if and only if cell $z$ of
$S$ is allocated. No distinctness of $x$, $y$ and the successor of $y$ is assumed.
