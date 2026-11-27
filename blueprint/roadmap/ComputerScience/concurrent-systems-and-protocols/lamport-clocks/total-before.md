# Lamport's total order

Fix a linear order on the processes. In an execution
$e_0, \dots, e_{n-1}$ with Lamport timestamps $t_0, \dots, t_{n-1}$, position $a$ precedes
position $b$ when $a < n$, $b < n$, and either $t_a < t_b$, or $t_a = t_b$ and the process of
$e_a$ is smaller than the process of $e_b$.

## Sources

- L. Lamport, *Time, Clocks, and the Ordering of Events in a Distributed System*, Communications of the ACM 21(7), July 1978, 558–565: "Ordering the Events Totally", the relation ⇒, p. 561.
