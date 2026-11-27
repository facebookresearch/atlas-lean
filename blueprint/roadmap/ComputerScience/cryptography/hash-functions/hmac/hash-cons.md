# Moving the first block into the chaining value

Let $h : S \times B \to S$ with blocks $B = \{0,1\}^n$, $\ell : \mathbb{N} \to B$ and $\mathrm{iv} \in S$. Write $\mathrm{chain}_z(x_1, \dots, x_r)$ for the chaining value $z_r$ with $z_0 = z$ and $z_i = h(z_{i-1}, x_i)$, and $\mathrm{MD}(x_1, \dots, x_r) = h(\mathrm{chain}_{\mathrm{iv}}(x_1, \dots, x_r), \ell(r))$ for the block-level Merkle–Damgård hash. For every block $x$ and blocks $x_1, \dots, x_r$,

$$
\mathrm{MD}(x, x_1, \dots, x_r) = h\bigl(\mathrm{chain}_{h(\mathrm{iv}, x)}(x_1, \dots, x_r),\ \ell(r + 1)\bigr).
$$

The first block moves into the initial chaining value, while the final length block still counts it: the count is $r + 1$, not $r$.
