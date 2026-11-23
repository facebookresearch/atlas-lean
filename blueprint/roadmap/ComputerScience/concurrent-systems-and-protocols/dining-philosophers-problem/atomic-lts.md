# Dining philosophers with atomic fork acquisition

The labelled transition system on the
states of the three philosophers, labelled by the philosopher that moves: there is a step
labelled $i$ from $s$ to $t$ exactly when either philosopher $i$ thinks in $s$, neither of its
forks $i$ and $i + 1$ (modulo $3$) is held in $s$, and $t$ is $s$ with philosopher $i$ eating;
or philosopher $i$ eats in $s$ and $t$ is $s$ with philosopher $i$ thinking. A fork is held as
in the naive protocol: philosopher $j$ holds fork $j$ when it holds its first fork or eats, and
holds fork $j + 1$ when it eats.
