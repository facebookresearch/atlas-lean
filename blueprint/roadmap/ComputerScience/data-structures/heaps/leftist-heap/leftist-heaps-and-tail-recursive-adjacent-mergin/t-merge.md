# Cost of merging leftist heaps

Over a linear order, the cost of merging two leftist heaps $h_1$ and $h_2$ is their auxiliary
merge cost with fuel equal to the size of $h_1$ plus the size of $h_2$. This fuel never runs out,
so the cost is the number of merge steps along the right spines: each step counts $1$ and moves
down the right spine of the heap whose root is chosen.
