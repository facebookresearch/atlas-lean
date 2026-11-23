# Dining philosophers with a butler

The labelled transition system on the states of the
three philosophers, labelled by the philosopher that moves: there is a step labelled $i$ from
$s$ to $t$ exactly when philosopher $i$ can move in $s$ under the naive protocol, if
philosopher $i$ is thinking then fewer than two philosophers hold a fork in $s$, and $t$ is $s$
with philosopher $i$ advanced one phase (thinking to holding its first fork, to eating, to
thinking). Under the naive protocol each philosopher $i$ picks up the left fork $i$ first and
then the right fork $i + 1$ (modulo $3$), each only when no philosopher holds it, and an eating
philosopher can always put both forks down.
