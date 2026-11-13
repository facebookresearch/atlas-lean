# Matrix powers of a stochastic matrix

For a stochastic matrix $P$ on the finite state
space $\{0, 1, \dots, M\}$ and $n \in \mathbb{N}$, the $n$-th matrix power $P^n$ is defined by
$P^0 = I$, the identity matrix, and $(P^{n+1})_{ij} = \sum_k P(i, k) (P^n)_{kj}$. The entry
$(P^n)_{ij}$ is the probability of moving from state $i$ to state $j$ in exactly $n$ steps.
