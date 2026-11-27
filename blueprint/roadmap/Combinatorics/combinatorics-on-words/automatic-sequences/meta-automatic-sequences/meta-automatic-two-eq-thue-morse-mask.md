# $\mathcal{M}_2$ is the Thue–Morse sequence along a binary digit mask

For a natural
number $m$ with binary digits $b_i = \lfloor m / 2^i \rfloor \bmod 2$, let $q(m)$ be the sum of
$b_i 2^i$ over the $i \le m$ with $i \not\equiv 2 \pmod 3$, that is, the number obtained from $m$
by setting its binary digits in the positions $i \equiv 2 \pmod 3$ to zero. Then for every natural
number $n$, the meta-automatic sequence $\mathcal{M}_2$ and the Thue–Morse sequence $t$ satisfy
$\mathcal{M}_2(n) = t(q(n))$. Moreover, writing the base-$4$ digits of $n$ as
$d_k = \lfloor n / 4^k \rfloor \bmod 4 = 2 j_k + i_k$ with $i_k, j_k \in \{0, 1\}$, we have
$q(n) = \sum_{k=0}^{n} d'_k 4^k$, where $d'_k = d_k$ if $k \equiv 0 \pmod 3$, $d'_k = 2 j_k$ if
$k \equiv 1 \pmod 3$, and $d'_k = i_k$ if $k \equiv 2 \pmod 3$.

## Sources

- John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of Integer Sequences 29 (2026), Article 26.4.1, Theorem 26 (`jis-2026-26.4.1-thm-26`).
