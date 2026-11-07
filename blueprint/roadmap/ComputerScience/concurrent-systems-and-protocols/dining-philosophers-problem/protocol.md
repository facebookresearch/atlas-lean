# Dining-philosophers protocol

A protocol for three philosophers $i \in \{0, 1, 2\}$
sitting between forks $0, 1, 2$ consists of two maps $\mathrm{first}, \mathrm{second}$ from
$\{0, 1, 2\}$ to itself, the fork philosopher $i$ picks up first and the one it picks up
second, such that for every $i$ these are its two neighbouring forks $i$ and $i + 1$
(modulo $3$) in some order: either $\mathrm{first}(i) = i$ and $\mathrm{second}(i) = i + 1$,
or $\mathrm{first}(i) = i + 1$ and $\mathrm{second}(i) = i$.
