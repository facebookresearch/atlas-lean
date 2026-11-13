# Syndrome table of the Hamming (7,4) code

Number the positions of a word in
$\mathbb{F}_2^7$ as $1, \dots, 7$. For a syndrome $s = (s_0, s_1, s_2) \in \mathbb{F}_2^3$,
read each $s_i$ as $0$ or $1$ and let $p = s_0 + 2 s_1 + 4 s_2$. The table sends $s$ to the zero
word if $p = 0$, and otherwise to the word whose only nonzero entry is a $1$ at position $p$.

The Hamming decoder subtracts from a received word the table entry of its syndrome; over
$\mathbb{F}_2$ this flips the bit at the position the syndrome names.
