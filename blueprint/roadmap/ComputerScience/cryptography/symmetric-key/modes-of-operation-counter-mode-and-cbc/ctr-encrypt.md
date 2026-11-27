# Counter-mode encryption

Let $Y$ be an additive commutative group of blocks. For a function $f \colon \mathbb{Z}/N \to Y$, a message $m \in Y^\ell$ and an initial counter $\mathrm{ctr} \in \mathbb{Z}/N$, counter-mode encryption returns

$$
(\mathrm{ctr},\ \mathrm{keystream}(f, \mathrm{ctr}) + m), \qquad \mathrm{keystream}(f, \mathrm{ctr})_i = f(\mathrm{ctr} + i) \quad (i < \ell).
$$

The keystream starts at $\mathrm{ctr}$ itself rather than at $\mathrm{ctr} + 1$ (Katz and Lindell, Section 3.6.2, with XOR replaced by the group addition).
