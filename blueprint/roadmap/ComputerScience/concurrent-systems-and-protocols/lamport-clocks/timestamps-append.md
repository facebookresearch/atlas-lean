# Appending events does not change earlier timestamps

Let $e_0, \dots, e_{n-1}$ be an
execution, and extend it by appending further events. For every $i < n$, the Lamport timestamp
of the event at position $i$ is the same in the extended execution as in the original one.
