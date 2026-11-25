# Matrix-chain ordering

Given $n \ge 1$ and natural numbers $p_0, \dots, p_n$, where matrix
$i$ of the chain ($0 \le i < n$) has $p_i$ rows and $p_{i+1}$ columns, the algorithm computes,
bottom-up by interval length, values $m_{i,j}$ for $0 \le i \le j < n$: $m_{i,i} = 0$ and, for
$i < j$, $m_{i,j}$ is the least value of $m_{i,k} + m_{k+1,j} + p_i p_{k+1} p_{j+1}$ over
$i \le k < j$, and the first split point $k$ attaining it is recorded. It then rebuilds a
parenthesization of the whole chain from the recorded split points and returns $m_{0,n-1}$
together with this parenthesization. One event is charged per evaluated split candidate and one
per reconstructed tree node.
