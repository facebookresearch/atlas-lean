# The odd-even merger merges

Let $k \in \mathbb{N}$ and let $f$ assign a Boolean value to
each wire $0, 1, 2, \dots$, with false read as $0$ and true as $1$. Let $a, c \le 2^k$ be such
that wires $0, \dots, 2^k - 1$ hold $a$ zeros followed by ones (wire $i < 2^k$ holds $0$ exactly
when $i < a$) and wires $2^k, \dots, 2^{k+1} - 1$ hold $c$ zeros followed by ones (wire
$2^k + i$, for $i < 2^k$, holds $0$ exactly when $i < c$). Then after Batcher's odd-even merger
on $2^{k+1}$ wires runs on $f$, every wire $j < 2^{k+1}$ holds $0$ exactly when $j < a + c$.
