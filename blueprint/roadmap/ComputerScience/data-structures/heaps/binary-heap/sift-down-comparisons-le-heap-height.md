# Sift-down makes at most two comparisons per unit of height of its start

For every array
$a$ over a linearly ordered type, of length $n$, and every index $i$, the number of value
comparisons counted by timed sift-down from $i$ is at most twice the height of $i$ in the
level-order binary tree with $n$ nodes, $2 \lfloor \log_2 \lfloor n/(i+1) \rfloor \rfloor$ (which
is $0$ when $i \ge n$).
