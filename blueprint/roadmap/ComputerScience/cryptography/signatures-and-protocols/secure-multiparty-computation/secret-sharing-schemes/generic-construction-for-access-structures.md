# Secret sharing for every monotone access structure

Let $\mathcal{A}$ be any monotone access structure on a finite set of parties, that is, an upward-closed family of coalitions (the authorized ones), in which the empty coalition is unauthorized, and let the secret be a bit $z \in \{0, 1\}$. The *generic construction* (of Ito, Saito and Nishizeki) shares $z$ by additively sharing it over $\mathbb{Z}_2$ (as an exclusive-or of random bits), independently for every authorized coalition $J \in \mathcal{A}$, among the members of $J$, and giving each party all its pieces. Then every authorized coalition reconstructs $z$ (from the pieces of any authorized subcoalition $J$), and with uniform random bits every unauthorized coalition sees a uniformly distributed view, independent of the secret. The share size can be exponential in the number of parties.

## Proof sketch

An unauthorized coalition $S$ misses at least one member of every authorized $J$, so its pieces of each additive sharing are uniform and independent; the independent sharings for different $J$ make the whole view uniform.

## Proof depends on

- [Additive $n$-out-of-$n$ secret sharing](additive-secret-sharing.md)

## Sources

- Amos Beimel, "Secret-Sharing Schemes: A Survey", Coding and Cryptology, Lecture Notes in Computer Science, Springer, 2011, pp. 11–46, Section 3.3 (the construction of Ito, Saito and Nishizeki).
