# Correctness and privacy of linear secret sharing from monotone span programs

For a monotone span program $\{M_P\}$ over a finite field: (i) every accepted coalition reconstructs the secret with its recombination vector; (ii) for every coalition $S$ that is not accepted and every translation-invariant key distribution, the view of $S$ is the same for all secrets: since $e_1 \notin \mathrm{rowspan}(M_S)$ there is a vector $w$ with $M_S w = 0$ and $w_1 = 1$, and translating the key by $(z' - z)w$ carries the view on $z$ to the view on $z'$. A share whose matrix has first column zero is independent of the secret. Hence the scheme is perfectly correct and perfectly private for the access structure of accepted coalitions; Shamir sharing is the case of Vandermonde rows.

## Proof sketch

(i) $\lambda^{\mathsf T} M_S (z, \rho)^{\mathsf T} = e_1^{\mathsf T}(z, \rho)^{\mathsf T} = z$. (ii) Linear algebra duality: $e_1$ is not in the row span exactly when it is not orthogonal to the kernel.

## Depends on

- [Monotone span programs and linear secret sharing](monotone-span-programs.md)

## Sources

- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
