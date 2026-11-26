# Tight quantum query bound for finding collisions in a random function

For a uniformly random $H:\{0,1\}^{n}\to\{0,1\}^{m}$ with $2^{n}\ge 2^{m/3}$, every quantum algorithm making $q$ queries finds $x\ne x'$ with $H(x)=H(x')$ with probability $O(q^{3}/2^{m})$. This is tight by the Brassard–Høyer–Tapp algorithm, and implies that collision resistance in the QROM requires output length $m\ge 3\lambda$ for $\lambda$ bits of security. Analogously, finding a preimage of a fixed $y$ succeeds with probability $O(q^{2}/2^{m})$, matching Grover search.

## Proof sketch

With the compressed oracle, bound the norm of the part of the state whose database contains a collision. A query adds at most one new entry, uniformly distributed; the amplitude of creating a collision with one of at most $q$ existing entries is $O(\sqrt{q/2^{m}})$ per query. Summing amplitudes over $q$ queries gives $O(q\sqrt{q/2^{m}})$, i.e., probability $O(q^{3}/2^{m})$, and the recording lemma converts this to the adversary's success probability.

## Depends on

- [Recording quantum queries: the database explains the adversary's output](compressed-oracle-recording.md)
- [Lower bound for quantum search (BBBV)](../../../quantum-algorithms/lower-bound-for-quantum-search/mul-card-le-of-forall-success.md)

## Proof depends on

- [Recording quantum queries: the database explains the adversary's output](compressed-oracle-recording.md)

## Sources

- Mark Zhandry, "How to Record Quantum Queries, and Applications to Quantum Indifferentiability", CRYPTO (2019), IACR ePrint 2018/276.
