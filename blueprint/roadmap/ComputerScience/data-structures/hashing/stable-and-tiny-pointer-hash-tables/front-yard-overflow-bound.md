# Chernoff bound on front-yard overflow

Throw $n$ keys independently and uniformly into $n/h$ bins, so each bin has mean load $h$. For $0 < \varepsilon \le 1$, the expected number of keys that land in a bin receiving more than $(1 + \varepsilon)h + 1$ keys is at most $n \exp(-\varepsilon^2 h / 3)$. In particular, with mean bin load $h = \Theta(\log n)$ and fixed $\varepsilon$, the expected back-yard size of a static set of keys is $O(n^{1-c})$ for some $c > 0$ depending on $\varepsilon$ and the constant in $h$. For dynamic sequences, the Iceberg Lemma of Bender et al. gives the stronger bound used by Iceberg hashing: with threshold $h + k\sqrt{h \log h}$ and $h \le \mathrm{polylog}\, n$, at every time at most $n/\mathrm{poly}(h)$ balls are exposed, with probability $1 - 2^{-n/\mathrm{polylog}\, n}$, against an oblivious sequence of insertions and deletions.

## Proof sketch

Fix a key; the number of other keys in its bin is binomial with $n - 1$ trials and success probability $h/n$, hence mean at most $h$. The multiplicative Chernoff bound gives probability at most $\exp(-\varepsilon^2 h/3)$ that it exceeds $(1+\varepsilon)h$. Summing over the $n$ keys gives the expectation bound.

## Depends on

- [Front-yard and back-yard hash table design](front-yard-back-yard-paradigm.md)

## Sources

- Michael A. Bender, Alex Conway, Martín Farach-Colton, William Kuszmaul, Guido Tagliavini, "Iceberg Hashing: Optimizing Many Hash-Table Criteria at Once", Journal of the ACM 70(6) (2023), arXiv:2109.04548.
