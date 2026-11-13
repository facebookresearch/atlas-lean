# Lamport timestamps

The Lamport timestamps $t_0, \dots, t_{n-1}$ of an execution
$e_0, \dots, e_{n-1}$ are computed by Lamport's clock algorithm. Every process keeps a
counter, initially $0$. For $k = 0, \dots, n-1$ in turn, let $c$ be the current counter of
the process of $e_k$, and let $m = t_i$ if $e_k$ receives the message sent by the event at
position $i$ with $i < k$, and $m = 0$ otherwise. Then $t_k = \max(c, m) + 1$, and the
counter of the process of $e_k$ is set to $t_k$.
