# Several independent keys of a pseudorandom function

Let $F$ be a PRF with domain $\{0,1\}^b$, keys and outputs in $\{0,1\}^k$ (the setting of the cascade), and $Q$ a polynomial. An adversary making $q$ queries in total, given oracle access to $F(k_1, \cdot), \dots, F(k_Q, \cdot)$ for independent uniform keys, distinguishes them from $Q$ independent random functions with advantage at most $Q \cdot \varepsilon$, where $\varepsilon$ is the best PRF advantage of an adversary making at most $q$ queries whose running time exceeds that of the given one by at most $c\,(Qk + q \cdot \mathrm{Time}(F) + q(k + b)\log q)$, for a small constant $c$: the time of sampling $Q$ keys and answering the $q$ oracle queries with evaluations of $F$ or lazily sampled random-function values. Hence $Q$ independent keys of a secure PRF are jointly pseudorandom.

## Proof sketch

Hybrid over the keys: in hybrid $i$ the first $i$ oracles are random functions; the reduction plants its own oracle at a uniformly chosen position and simulates the others.

## Depends on

- [Asymptotic PRF security relative to a class of distinguishers](../pseudorandom-functions/prfsecure.md)

## Proof depends on

- [Hybrid argument](../../security-games/games-and-advantages/advantage-le-sum.md)

## Sources

- M. Bellare, R. Canetti and H. Krawczyk, "Pseudorandom Functions Revisited: The Cascade Construction and its Concrete Security", Proceedings of the 37th Annual Symposium on Foundations of Computer Science (FOCS 1996), IEEE, 1996, pp. 514–523; Lemma 3.3 of the full version (the $m$-oracle family $mF$, $m$ independent instances of $F$ against $m$ independent random functions, has $\varepsilon = m\varepsilon'$ with the running-time loss above; the proof is this hybrid).
