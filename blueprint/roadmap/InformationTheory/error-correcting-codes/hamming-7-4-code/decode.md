# Syndrome decoder of the Hamming code

Let $H$ be the $3 \times 7$ parity-check matrix of
the Hamming code over $\mathbb{F}_2$, whose column $j$, for $j = 1, \dots, 7$, is the binary
expansion of $j$, least significant bit first. Given a word $y \in \mathbb{F}_2^7$, compute its
syndrome $s = (s_0, s_1, s_2) = Hy \in \mathbb{F}_2^3$. If $s = 0$, return $y$. Otherwise read
the entries of $s$ as bits of the number $p = s_0 + 2s_1 + 4s_2 \in \{1, \dots, 7\}$ and return
$y$ with its $p$-th bit flipped, counting positions from $1$.
