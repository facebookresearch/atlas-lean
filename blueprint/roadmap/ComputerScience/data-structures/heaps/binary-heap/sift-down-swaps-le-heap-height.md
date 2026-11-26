# Sift-down performs at most as many swaps as the height of its start

For every array $a$
over a linearly ordered type, of length $n$, and every index $i$, the number of array swaps
counted by timed sift-down from $i$ is at most the height of $i$ in the level-order binary tree
with $n$ nodes, $\lfloor \log_2 \lfloor n/(i+1) \rfloor \rfloor$ (which is $0$ when $i \ge n$).
