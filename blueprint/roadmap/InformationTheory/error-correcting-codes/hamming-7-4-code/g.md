# Generator matrix of the Hamming (7,4) code

$G$ is the $4 \times 7$ matrix over
$\mathbb{F}_2$, with columns indexed by the positions $1, \dots, 7$, whose $k$-th row encodes the
$k$-th message bit: if $p$ is the $k$-th of the message positions $3, 5, 6, 7$, the row has
entry $1$ at position $p$ and at each of the parity positions $1, 2, 4$ that occurs in the
binary expansion of $p$, and entry $0$ elsewhere.

Explicitly, its rows are $1110000$, $1001100$, $0101010$ and $1101001$.
