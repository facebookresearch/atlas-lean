# Tight quantum query bound for finding collisions in a random function

Let $H:[M]\to[N]$ be a uniformly random function, with $N=2^{m}$ for $m$-bit outputs. For every domain size $M$, every quantum algorithm making $q$ queries outputs $x\ne x'$ with $H(x)=H(x')$ with probability at most $C(q+1)^{3}/N$ for a universal constant $C$. This bound is tight for constant success probability only when the domain is large enough to contain collisions: if $M=\Omega(\sqrt{N})$, an algorithm making $O(N^{1/3})$ queries (Ambainis's element-distinctness algorithm run on a random subset of about $\sqrt{N}/2$ inputs) finds a collision with constant probability, so the query complexity is $\Theta(N^{1/3})$; if $M=o(\sqrt{N})$, even the entire function has a collision with probability at most $\binom{M}{2}/N=o(1)$. Consequently, for domains of size $\Omega(2^{m/2})$, resisting constant-success quantum collision attacks with $2^{\lambda}$ queries requires output length $m\ge3\lambda-O(1)$. For preimages of a fixed $y$, the analogous bound is $O((q+1)^{2}/N)$; it matches Grover search only when the domain has size $\Omega(N)$, since otherwise a preimage exists with probability at most $M/N$.

## Proof sketch

With the compressed oracle, bound the norm of the part of the state whose database contains a collision. A query adds at most one new entry, uniformly distributed; the amplitude of creating a collision with one of at most $q$ existing entries is $O(\sqrt{q/2^{m}})$ per query. Summing amplitudes over $q$ queries gives $O(q\sqrt{q/2^{m}})$, i.e., probability $O(q^{3}/2^{m})$, and the recording lemma converts this to the adversary's success probability.

## Depends on

- [The quantum random oracle model](quantum-random-oracle-model.md)

## Proof depends on

- [Recording quantum queries: the database explains the adversary's output](compressed-oracle-recording.md)
- [Lower bound for quantum search (BBBV)](../../../quantum-algorithms/lower-bound-for-quantum-search/mul-card-le-of-forall-success.md)

## Sources

- Mark Zhandry, "A Note on the Quantum Collision and Set Equality Problems", Quantum Information and Computation 15 (2015), Theorems 1.1, 2.2 and 3.1, arXiv:1312.1027.
- Mark Zhandry, "How to Record Quantum Queries, and Applications to Quantum Indifferentiability", CRYPTO (2019), IACR ePrint 2018/276.
