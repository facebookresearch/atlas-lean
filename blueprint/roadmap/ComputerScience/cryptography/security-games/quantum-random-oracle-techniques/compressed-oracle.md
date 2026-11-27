# Zhandry's compressed oracle representation

Represent a uniformly random $H:\{0,1\}^{n}\to\{0,1\}^{m}$ as the uniform superposition $\bigotimes_x|\hat{0}\rangle$-transformed state $\sum_H|H\rangle$ held by the oracle and purify the adversary's interaction: querying applies $|x,y\rangle|H\rangle\mapsto|x,y\oplus H(x)\rangle|H\rangle$. In the Fourier basis (Hadamard on each output register), a query acts as a phase-kickback that changes the oracle's entry at $x$ only if the query register is not in state $0$. The *compressed oracle* stores this purified oracle as a database $D$ of at most $q$ pairs $(x,w)$, with entries returned to the empty symbol $\bot$ when they would be uniform, via a decompression isometry applied around each query. After $q$ queries the database contains at most $q$ entries, and the joint state of adversary and compressed oracle is perfectly indistinguishable from that with a real random oracle.

## Depends on

- [The quantum random oracle model](quantum-random-oracle-model.md)

## Sources

- Mark Zhandry, "How to Record Quantum Queries, and Applications to Quantum Indifferentiability", CRYPTO (2019), IACR ePrint 2018/276.
