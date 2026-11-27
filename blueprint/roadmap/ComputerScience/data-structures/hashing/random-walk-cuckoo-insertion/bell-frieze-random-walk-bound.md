# Random-walk cuckoo insertion takes constant expected time up to the load threshold

Let $d \ge 4$, let $c_d^* = \xi_d / \big(d\,(1 - e^{-\xi_d})^{d-1}\big)$, where $\xi_d > 0$ is the unique solution of $d = \frac{\xi(e^{\xi} - 1)}{e^{\xi} - 1 - \xi}$, and let $c < c_d^*$ and $n = cm$. With probability $1 - o(1)$ over the random hash functions, the expected insertion time of the uniform random walk (variant (a) of random-walk insertion, in which every key, the new one included, takes a uniform one of its $d$ candidates without inspecting the others) into a $d$-ary cuckoo table holding $n$ keys in $m$ slots is $O(1)$, a constant depending only on $c$ and $d$ but not on $m$. The bound is robust to $n^{\beta}$ oblivious insertions and deletions for a suitable constant $\beta > 0$.

## Proof sketch

Building on expansion properties of the bipartite hashing graph established by Fountoulakis, Panagiotou and Steger, Bell and Frieze introduce recursively defined sets $B_i$ of bad slots from which a random walk is unlikely to escape quickly, and show that below $c_d^*$ these sets are small and expand. Fix the matching produced by the earlier insertions. Averaged over the new key's fresh hash values and the uniform walk's random choices, the probability that the walk has not reached a free slot after $\ell$ steps decays faster than every inverse polynomial in $\ell$, outside an event of probability $o(1)$ over the hash functions. A tail bound $C\ell^{-2}$ already suffices: summing $\Pr[T > \ell] \le \min(1, C\ell^{-2})$ over $\ell \ge 0$ gives $\mathbb{E}[T] = O(1)$, which is their expected-time theorem. The argument does not give geometric decay from every fixed starting slot.

## Depends on

- [Random-walk insertion for d-ary cuckoo hashing](random-walk-cuckoo-insertion.md)
- [d-ary cuckoo hashing and its hashing graph](d-ary-cuckoo-hashing.md)

## Proof depends on

- [Sharp load thresholds for d-ary cuckoo hashing](cuckoo-load-threshold.md)

## Sources

- Tolson Bell, Alan Frieze, "O(1) Insertion for Random Walk d-ary Cuckoo Hashing up to the Load Threshold", FOCS (2024), Theorem I.1 (stated for $d \ge 4$), arXiv:2401.14394.
- Nikolaos Fountoulakis, Konstantinos Panagiotou, Angelika Steger, "On the Insertion Time of Cuckoo Hashing", SIAM Journal on Computing 42(6) (2013).
