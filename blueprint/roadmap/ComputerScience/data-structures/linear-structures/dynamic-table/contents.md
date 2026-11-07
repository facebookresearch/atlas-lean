# Contents of a dynamic table

Let $T$ be a dynamic table with slots $s_0, \dots, s_{m-1}$,
each empty or holding an item, and item count $n \le m$. The contents of $T$ is the array of the
items held by the occupied slots among $s_0, \dots, s_{n-1}$, in order; empty slots in this
prefix are skipped.

The insertion procedure never consults the contents.
