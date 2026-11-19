# Enabled moves under a butler

Philosopher $i$ can move in state $s$ when it can move in
$s$ under the naive protocol and, if it is thinking, fewer than two philosophers hold at least
one fork in $s$. Under the naive protocol each philosopher $i$ picks up the left fork $i$ first
and then the right fork $i + 1$ (modulo $3$), each only when no philosopher holds it, and an
eating philosopher can always put both forks down.
