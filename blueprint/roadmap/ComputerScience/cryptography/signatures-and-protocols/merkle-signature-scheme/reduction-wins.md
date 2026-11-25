# Core of the reduction to Lamport

Let messages be $\ell$-bit strings with $\ell \ge 1$. If the Merkle forger wins on the keys $sk'$
with $sk^*$ at index $j$ and on coins $r$, with a signature that carries the honest key and has
index $j$, then the reduction with coins $(j, sk', r)$ forges a Lamport signature under $sk^*$.
