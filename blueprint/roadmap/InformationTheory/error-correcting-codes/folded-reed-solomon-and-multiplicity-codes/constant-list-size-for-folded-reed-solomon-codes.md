# Kopparty-Ron-Zewi-Saraf-Wootters: constant list size up to capacity

Let $\varepsilon > 0$ and $\ell \in \mathbb{N}$, and let $C$ be a folded Reed-Solomon code with folding parameter $s$, a primitive element $\gamma$ of $\mathbb{F}_q$ and the classical evaluation points (distinct $\alpha_i \in \{\gamma^{sj} : 0 \le j < (q-1)/s\}$, so $n \le (q-1)/s$), encoding polynomials of degree less than $k$; it has rate $R = k/(sn)$ and relative distance at least $\delta := 1 - (k-1)/(sn) > 1 - R$. If $s \ge 16\ell/\varepsilon^2$, then $C$ is

$$
\Big(\delta - \varepsilon,\ \ell,\ (\ell/\varepsilon)^{O(\varepsilon^{-1}\log(\ell/(1-\delta)))}\Big)\text{-list recoverable},
$$

in particular $(1 - R - \varepsilon, \ell, L)$-list recoverable with that list size $L$, and for $\ell = 1$ (so $s \ge 16/\varepsilon^2$) it is list decodable up to radius $\delta - \varepsilon$ with list size $(1/\varepsilon)^{O(\varepsilon^{-1}\log(1/(1-\delta)))}$. For every $\eta > 0$ a randomized algorithm list recovers $C$ with these parameters with success probability at least $1 - \eta$ in time $\mathrm{poly}(\log q, s, k, n, L, \log(1/\eta))$. Univariate multiplicity codes also have constant list size: over a prime field $\mathbb{F}_p$ with $s \le p$, the multiplicity code of order $s$ with $n$ distinct evaluation points, degree less than $k$ and rate $R = k/(sn)$ is, if $s \ge 16\ell/\varepsilon^2$ and $4\ell/\varepsilon \le p$, $(\delta - \varepsilon, \ell, L)$-list recoverable with $\delta = 1 - (k-1)/(sn)$ and $L \le (\ell/\varepsilon)^{(4\ell/\varepsilon)(1 + (k-1)/p)}$. (The sources use Hasse derivatives; for $s \le p$ these differ from the ordinary derivatives of order $j < s$ by the invertible factors $j!$, so the two codes are equivalent.)

## Proof sketch

Starting from the Guruswami-Wang affine subspace of dimension $m - 1$, show that it contains only a constant number of codewords close to the received word: randomly restrict to a few coordinates where the received word agrees with the target codeword and use that FRS codes behave like subspace designs on such restrictions, so each restriction cuts the candidate subspace's dimension. An iterative pruning yields list size depending only on $\varepsilon$.

## Depends on

- [List recovery and relaxed generalized Singleton bounds](list-recovery-of-folded-codes.md)
- [Folded Reed-Solomon codes](folded-reed-solomon-codes.md)
- [Univariate multiplicity codes](univariate-multiplicity-codes.md)

## Proof depends on

- [Guruswami-Wang: the list of folded RS and multiplicity codes lies in a low-dimensional subspace](linear-algebraic-list-decoding-into-a-subspace.md)

## Sources

- Swastik Kopparty, Noga Ron-Zewi, Shubhangi Saraf, Mary Wootters, "Improved list decoding of folded Reed-Solomon and multiplicity codes", FOCS (2018), SIAM Journal on Computing 52(3) (2023); arXiv:1805.01498, ECCC TR18-091 (revision 2: Section 2, Theorem 3.11).
- Itzhak Tamo, "Tighter list-size bounds for list-decoding and recovery of folded Reed-Solomon and multiplicity codes", IEEE Transactions on Information Theory 70(12) (2024); arXiv:2312.17097 (Theorem 3.8).
