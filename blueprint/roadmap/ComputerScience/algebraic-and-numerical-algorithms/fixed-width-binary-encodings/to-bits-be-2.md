# Fixed-width big-endian encoding of a residue

The $w$-bit big-endian encoding of a residue $x \in \mathbb{Z}/N$ is the $w$-bit encoding of the natural
number $\mathrm{val}(x)$: for $N \ne 0$ this is the canonical representative of $x$ in $\{0, \dots, N - 1\}$,
and for $N = 0$, where $\mathbb{Z}/0 = \mathbb{Z}$, it is taken to be $|x|$. It is lossless when $N \ne 0$
and $N \le 2^w$, for example for serializing elements of $\mathbb{Z}_N$ in RSA (Katz and Lindell, 2nd ed.,
Section 11.5). The bound alone is not enough: for $N = 0$ it holds at every width, but
$\mathbb{Z}/0 = \mathbb{Z}$ is infinite, so no fixed width is lossless (stated here without proof).
