# Exact transition count of depth-first search

Let $G$ be a finite directed graph with
ordered adjacency lists $N(v)$, whose entries may repeat, and let $R$ be a list of roots, possibly
with repetitions. Run the depth-first search machine from $R$ (each transition drops a pending
vertex that is already visited, discovers a new vertex, or finishes a vertex). Let
$v_1, \dots, v_k$ be the preorder of the depth-first search of $G$ from $R$. Then there is a
terminal machine state, with no work left, whose recorded output is the depth-first traversal of
$G$ from $R$ and which is reached from the initial state in exactly
$|R| + k + \sum_{i=1}^{k} |N(v_i)|$ transitions, where $|R|$ is the length of $R$ and $|N(v)|$
is the length of the adjacency list of $v$.
