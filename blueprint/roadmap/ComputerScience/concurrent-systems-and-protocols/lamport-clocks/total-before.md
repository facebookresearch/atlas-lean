# Lamport's total order

Fix a linear order on the processes. In an execution
$e_0, \dots, e_{n-1}$ with Lamport timestamps $t_0, \dots, t_{n-1}$, position $a$ precedes
position $b$ when $a < n$, $b < n$, and either $t_a < t_b$, or $t_a = t_b$ and the process of
$e_a$ is smaller than the process of $e_b$.
