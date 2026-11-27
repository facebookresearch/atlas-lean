# Counter-mode decryption inverts encryption

Let $Y$ be an additive commutative group. For every $N$, every function $f \colon \mathbb{Z}/N \to Y$, every message $m \in Y^\ell$ and every counter $\mathrm{ctr}$,

$$
\mathrm{ctrDecrypt}(f, \mathrm{ctrEncrypt}(f, m, \mathrm{ctr})) = m,
$$

where [encryption](ctr-encrypt.md) returns $(\mathrm{ctr}, \mathrm{keystream}(f, \mathrm{ctr}) + m)$ and decryption of $(\mathrm{ctr}, c)$ subtracts the keystream of the returned counter on the right, $c - \mathrm{keystream}(f, \mathrm{ctr})$.
