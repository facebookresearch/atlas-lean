# Cuckoo hashing with O(log n)-wise independent hash pairs

Let the sub-table size $r$ satisfy $r \ge 32 \max(n, 4)$, let the eviction cap $L$ satisfy $L_0(n) \le L \le r$ for an explicit $L_0(n) = O(\log n)$, and let $h_1, h_2$ be independent $(2L + 2)$-wise independent hash functions into $[r]$. Then $(h_1, h_2)$ is a good cuckoo hash pair with absolute constants $C_{\mathrm{walk}}$ and $C_{\mathrm{reh}}$, independent of $n$, $r$ and $L$. The same holds for uniformly random functions, for $(2L+2)$-wise independent polynomial hash pairs, and for double tabulation hash pairs $h_i = h_{i,1} \circ h_{i,0}$ into $[r]$ with $r = 2^M$, keys in $\Sigma^c$ and $d$ derived characters, conditioned on both first stages $h_{1,0}, h_{2,0}$ being $(2L+2)$-unique, with the same constants (the condition makes each $h_i$ $(2L+2)$-wise independent over its second-stage tables). By Thorup's Theorem 1, if $d \ge 6c$ and $2L + 2 \le |\Sigma|^{1/(5c)}$, fully random first-stage tables satisfy the condition with probability $1 - o(|\Sigma|^{2 - d/(2c)})$, asymptotically in $|\Sigma|$ under his assumptions $c = |\Sigma|^{o(1)}$ and $(c + d)^c = |\Sigma|^{o(1)}$.

Pagh and Rodler prove the asymptotic form of these bounds for $r \ge (1+\varepsilon) n$ and an eviction cap $\lceil 3 \log_{1+\varepsilon} r \rceil$, using only that the hash pair behaves as fully random on every set of at most MaxLoop keys (their Section 2.3, with Siegel's functions). At $1 + \varepsilon = 32$ their bound (3) on the expected number of iterations evaluates to $1 + 2/(1 - 32^{-2/3}) + O(\log n / n^2) \approx 3.22$, so the walk constant this argument yields exceeds $3$. The explicit thresholds $r \ge 32\max(n,4)$ and $L_0(n)$, any specific values of the constants, and the instantiations by polynomial hashing and double tabulation are not stated in the cited sources.

## Proof sketch

A displacement walk of length $t$ yields a simple path of about $t/3$ distinct keys, and an insertion failure yields a component with two cycles; both involve at most $2L+2$ keys. Under $(2L+2)$-wise independence each fixed path or bicyclic configuration of $\ell$ edges occurs with probability $r^{-\ell}$ times a combinatorial factor, and since $r \ge 32 n$ the expected number of such configurations decays geometrically in $\ell$. Summing over $\ell$ gives the walk bound, the $O(1/n^2)$ failure bound and failure probability at most $1/2$ for a whole set.

## Depends on

- [Good cuckoo hash-pair contract](good-cuckoo-hash-pair-contract.md)
- [k-wise independent hash family](../word-ram-hash-families/k-wise-independent-hash-family.md)
- [Polynomial hashing over GF(2^q) is k-wise independent](../word-ram-hash-families/polynomial-hashing-is-k-wise-independent.md)
- [Double tabulation hashing](../word-ram-hash-families/double-tabulation-hashing.md)

## Proof depends on

- [Structure of cuckoo displacement walks](structure-of-cuckoo-walks.md)
- [Thorup's high independence of double tabulation](../word-ram-hash-families/high-independence-of-double-tabulation.md)

## Sources

- R. Pagh and F. F. Rodler, "Cuckoo Hashing", Journal of Algorithms 51(2), 2004 (Lemma 1 and Section 2.3).
- M. Thorup, "Simple Tabulation, Fast Expanders, Double Tabulation, and High Independence", Proceedings of the 54th IEEE Symposium on Foundations of Computer Science (FOCS), 2013; arXiv:1311.3121.
