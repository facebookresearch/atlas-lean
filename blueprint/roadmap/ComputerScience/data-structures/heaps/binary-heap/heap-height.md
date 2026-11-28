# Height of a node in a level-order binary tree

For natural numbers $n$ and $i$, the height
of the index $i$ in the binary tree with $n$ nodes stored in level order at the indices
$0, \dots, n - 1$ is $\lfloor \log_2 \lfloor n/(i+1) \rfloor \rfloor$, where
$\lfloor \log_2 0 \rfloor$ is read as $0$. For $i < n$ this is the largest $d$ with
$(i+1) 2^d \le n$, and for $i \ge n$ it is $0$.
