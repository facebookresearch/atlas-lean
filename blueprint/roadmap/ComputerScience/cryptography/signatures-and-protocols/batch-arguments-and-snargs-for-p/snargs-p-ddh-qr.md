# SNARGs for P from sub-exponential DDH and quadratic residuosity

Assuming jointly the sub-exponential hardness of the decisional Diffie–Hellman assumption and of the quadratic residuosity assumption, there are publicly verifiable SNARGs in the common reference string model for every language decidable in deterministic time $T$, with communication complexity and verifier running time $n\cdot T^{o(1)}$ for instances of length $n$, and prover time $\mathrm{poly}(T)$; for languages decidable in nondeterministic time $T$ and space $S$ the communication and verifier time are $(n+S)\cdot T^{o(1)}$. In particular SNARGs for P with these bounds do not need lattice assumptions or pairings.

## Proof sketch

Split a time-$T$ computation into $k$ subcomputations of time $T/k$ and recursively prove them with an interactive argument in which the prover commits, with a somewhere extractable commitment with local openings, to the messages of all $k$ sub-arguments and then proves with a batch argument for NP that all committed transcripts are accepting. Instantiate the batch arguments with Fiat–Shamir-compatible interactive batch arguments for NP based on quadratic residuosity, show that the recursive argument stays Fiat–Shamir compatible, and remove interaction with correlation-intractable hash functions for low-depth threshold circuits from sub-exponential DDH. This gives the nondeterministic bounded-space result, and a compiler from bounded-space SNARGs gives the result for deterministic time.

## Depends on

- [Advantage of a DDH distinguisher](../../public-key/elgamal-encryption/ddh-advantage.md)
- [Residuosity advantage](../../public-key/goldwasser-micali-encryption/qr-advantage.md)

## Proof depends on

- [Non-interactive batch arguments for NP](batch-argument.md)
- [Somewhere extractable (somewhere statistically binding) hash functions](somewhere-extractable-hash.md)
- [Correlation-intractable hash families](correlation-intractability.md)

## Sources

- James Hulett, Ruta Jawale, Dakshita Khurana, Akshayaram Srinivasan, "SNARGs for P from Sub-exponential DDH and QR", EUROCRYPT (2022), abstract, Section 1.1 and Section 2.1.
