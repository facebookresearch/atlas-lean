# Offline dictionary attack against hashed passwords

Let $H$ be a hash function (given as an oracle) and $D$ a dictionary of candidate passwords. Given $v = H(\mathrm{pw})$ with $\mathrm{pw} \in D$, searching $D$ in order and returning the first $w$ with $H(w) = v$ returns a password with the same hash as $\mathrm{pw}$ (possibly $\mathrm{pw}$ itself), using at most $|D|$ evaluations of $H$. If passwords are drawn from a distribution $\mu$, the attack succeeds with probability at least $\mu(D)$.

## Proof sketch

The true password is in $D$, so the search stops at or before it.

## Depends on

- [Adaptive oracle algorithms](../../security-games/oracle-algorithms/oracle-comp.md)

## Sources

- A. J. Menezes, P. C. van Oorschot and S. A. Vanstone, "Handbook of Applied Cryptography", CRC Press, 1996, §10.2.2(ii)–(iii).
