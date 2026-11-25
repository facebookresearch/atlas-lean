# Odd-even merge sort sorts every $0$-$1$ input

Let $k \in \mathbb{N}$ and let $f$ assign a
Boolean value to each wire $0, 1, 2, \dots$, with false read as $0$ and true as $1$. After
Batcher's odd-even merge sort on $2^k$ wires runs on $f$, there is $z \le 2^k$ such that every
wire $j < 2^k$ holds $0$ exactly when $j < z$: wires $0, \dots, 2^k - 1$ hold $z$ zeros followed
by ones.
