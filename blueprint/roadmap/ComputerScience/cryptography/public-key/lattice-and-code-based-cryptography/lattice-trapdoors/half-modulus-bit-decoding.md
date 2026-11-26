# Half-modulus encoding of a bit tolerates errors below $q/4$

Let $q = 2^w$ with $w \ge 1$. Encode a bit $\mu$ as $\mu \cdot 2^{w-1} \in \mathbb{Z}_q$ and decode a residue $x$ to $1$ exactly when its canonical representative lies in $[q/4, 3q/4)$. Then for every integer error $e$ with $4|e| < q$, decoding $\mu\, 2^{w-1} + e \bmod q$ returns $\mu$. Equivalently, the decoded bit is the exclusive-or of the two most significant bits of the residue. Moreover, if each $e_i$ satisfies $|e_i| \le B$, then any subset sum $\sum_{i \in S} e_i$ has absolute value at most $|S| B$, which is how decryption noise is bounded in Regev-type schemes.

## Proof sketch

For $\mu = 0$ the representative of $e$ lies in $[0, q/4) \cup (3q/4, q)$; for $\mu = 1$ the representative of $q/2 + e$ lies in $(q/4, 3q/4)$.

## Sources

- Oded Regev, "On Lattices, Learning with Errors, Random Linear Codes, and Cryptography", Journal of the ACM, 2009.
- Chris Peikert, "A Decade of Lattice Cryptography", Foundations and Trends in Theoretical Computer Science, 2016.
