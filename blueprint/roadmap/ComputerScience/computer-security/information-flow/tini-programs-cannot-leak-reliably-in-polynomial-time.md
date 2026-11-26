# Termination-insensitive noninterference cannot leak a secret reliably in polynomial time

Bound secrets to $N$ bits, $0 \le H < 2^N$, and let $\mathrm{Obs}_N$ and $k_N$ restrict observations and knowledge to such secrets. An attacker is a pair of families
$(\{L_n\}, \{t_n\})$ choosing, for each secret size $N$, a low input $L_N$ and an observation time $t_N$. A program $C$ *leaks reliably* for this attacker if for every
$N$ and every $H \in \{0, \dots, 2^N - 1\}$ some $\vec\alpha \in \mathrm{Obs}_N(C, L_N)$ with $|\vec\alpha| \le t_N$ has $k_N(C, L_N, \vec\alpha) = \{H\}$.

**Theorem.** If $C$ satisfies [termination-insensitive noninterference](termination-insensitive-noninterference-for-programs-with-output.md) and leaks reliably for an
attacker with running times $\{t_n\}$, then $t_N \ge 2^N - 1$ for every $N$. In particular a TINI program does not leak reliably within any polynomial running time. The exponential order of the bound is attained by brute force: the program that outputs
$i = 0, 1, 2, \dots$ in turn and diverges when $i$ equals the secret satisfies TINI and reveals any $N$-bit secret within about $2^N$ observations, counting the
observation that no further output follows.

The proof labels the tree of observations of length at most $t_N$ by knowledge sets and shows that under TINI it has at most $t_N + 1$ leaves.

## Depends on

- [Termination-insensitive noninterference for programs with output](termination-insensitive-noninterference-for-programs-with-output.md)

## Sources

- A. Askarov, S. Hunt, A. Sabelfeld and D. Sands, "Termination-insensitive noninterference leaks more than just a bit", *Computer Security – ESORICS 2008*, Springer, 2008, copy at <https://www.cse.chalmers.se/~andrei/esorics08.pdf>: Section 4, Definitions 6–10, Lemma 2, Proposition 1 on knowledge trees and Theorem 2 with its proof; Section 1 (program 2), Section 3 (Theorem 1 and the typing of program 2) and Section 4 (Definition 9 and Figure 4(b), which count the no-further-output observation).
