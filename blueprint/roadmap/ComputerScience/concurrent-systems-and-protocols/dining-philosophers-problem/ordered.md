# Resource-ordered dining-philosophers protocol

The protocol in which every philosopher
$i \in \{0, 1, 2\}$ picks up the lower-numbered of its two forks $i$ and $i + 1$ (modulo $3$)
first and the higher-numbered one second: philosophers $0$ and $1$ take fork $i$ first, and
philosopher $2$ takes fork $0$ first and fork $2$ second.
