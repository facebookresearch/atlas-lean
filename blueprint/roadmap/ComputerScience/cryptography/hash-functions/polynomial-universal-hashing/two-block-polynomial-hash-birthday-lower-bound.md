# Two-block polynomial hashing collides with constant probability at the birthday scale

Let $F$ be a finite field (more generally a finite ring) with $|F| \ge 16$, fix any key $k$, and let $q = \lfloor \sqrt{|F|} \rfloor$. Draw $q$ independent uniform two-block messages $m_1, \dots, m_q \in F \times F$ and hash each with the variable-length polynomial hash $H_{\mathrm{poly}}(k, (a_1, a_2)) = k^2 + a_1 k + a_2$. With probability at least $1/8$ there exist $i, j$ with $m_i \ne m_j$ and $H_{\mathrm{poly}}(k, m_i) = H_{\mathrm{poly}}(k, m_j)$.

## Proof sketch

For fixed $k$, the hash of a uniform two-block message is uniform on $F$ (adding a uniform $a_2$ is a translation of the additive group), so the $q$ digests are independent and uniform on $F$. With $N = |F|$ they are pairwise distinct with probability $\prod_{i<q}(1 - i/N) \le e^{-q(q-1)/(2N)}$. Since $q \ge 4$ and $N < (q+1)^2$, $q(q-1)/(2N) > q(q-1)/(2(q+1)^2) \ge 6/25$, so some two digests coincide with probability at least $1 - e^{-6/25} > 0.2$. Two sampled messages are equal with probability at most $\binom{q}{2}/N^2 \le 1/(2N) \le 1/32$, which leaves more than $1/8$.

## Depends on

- [Carter–Wegman MACs](../../symmetric-key/macs-and-modes/carterwegman-macs.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", version 0.6, 2023.
