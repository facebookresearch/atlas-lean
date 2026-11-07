# Run of Lloyd's algorithm

Let $x_i$ ($i \in \iota$, a finite index set) be points in a
real inner product space $E$. Sequences of assignments $a_t : \iota \to \{0, \dots, k-1\}$ and of
centers $c_t : \{0, \dots, k-1\} \to E$, indexed by $t \in \mathbb{N}$, form a run of Lloyd's
algorithm when for every $t$: for each $j < k$ the center $c_{t+1}(j)$ is the centroid of the
cluster $\{i : a_t(i) = j\}$ (the zero vector if this cluster is empty), and $a_{t+1}$ assigns
every point to a nearest center of $c_{t+1}$. The initial assignment $a_0$ and centers $c_0$ are
arbitrary.
