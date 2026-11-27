# Two-block polynomial hashing collides with constant probability at the birthday scale

Let $F$ be a finite field (more generally a finite ring) with $|F| \ge 16$, fix any key $k$, and let $q = \lfloor \sqrt{|F|} \rfloor$. Draw $q$ independent uniform two-block messages $m_1, \dots, m_q \in F \times F$ and hash each with the variable-length polynomial hash $H_{\mathrm{poly}}(k, (a_1, a_2)) = k^2 + a_1 k + a_2$. With probability at least $1/8$ there exist $i, j$ with $m_i \ne m_j$ and $H_{\mathrm{poly}}(k, m_i) = H_{\mathrm{poly}}(k, m_j)$.

## Proof sketch

For fixed $k$, the hash of a uniform two-block message is uniform on $F$ (adding a uniform $a_2$ is a translation of the additive group), so the birthday lower bound gives a collision among digests with probability at least about $1 - e^{-q(q-1)/(2|F|)}$. Subtracting the probability that two sampled messages are equal, at most $\binom{q}{2}/|F|^2$, leaves at least $1/8$ once $|F| \ge 16$.

## Depends on

- [Birthday lower bound](../birthday-bound/collision-prob-ge.md)
- [Carter–Wegman MACs](../../symmetric-key/macs-and-modes/carterwegman-macs.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", version 0.6, 2023.
