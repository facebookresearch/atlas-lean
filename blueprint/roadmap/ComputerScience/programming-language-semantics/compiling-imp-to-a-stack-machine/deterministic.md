# Determinism of the stack machine

For every program $P$, the step relation of the stack
machine running $P$ is deterministic: if a configuration $x$ steps to $y$ and to $z$, then
$y = z$. The fetched instruction and the shape of the stack determine the next configuration.
