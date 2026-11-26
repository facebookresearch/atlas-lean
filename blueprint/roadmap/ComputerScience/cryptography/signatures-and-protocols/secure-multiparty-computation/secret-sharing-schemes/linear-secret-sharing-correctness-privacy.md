# Correctness and privacy of linear secret sharing from monotone span programs

For a monotone span program $\{M_P\}$ over a finite field: (i) every accepted coalition reconstructs the secret with its recombination vector; (ii) for every coalition $S$ that is not accepted, the view of $S$ under uniform $\rho$ is the same for all secrets: since $e_1 \notin \mathrm{rowspan}(M_S)$ there is a vector $w$ with $M_S w = 0$ and $w_1 = 1$, and the map $(z, \rho) \mapsto (z, \rho) + (z' - z)w$, which translates $\rho$ and so preserves its uniform law, carries the view on $z$ to the view on $z'$. A share whose matrix has first column zero is independent of the secret. Hence the accepted coalitions recover the secret and every other coalition's view is independent of it; Shamir sharing is the case of Vandermonde rows.

## Proof sketch

(i) $\lambda^{\mathsf T} M_S (z, \rho)^{\mathsf T} = e_1^{\mathsf T}(z, \rho)^{\mathsf T} = z$. (ii) Linear algebra duality: $e_1$ is not in the row span exactly when it is not orthogonal to the kernel.

## Depends on

- [Monotone span programs and linear secret sharing](monotone-span-programs.md)

## Sources

- Amos Beimel, "Secret-Sharing Schemes: A Survey", Coding and Cryptology, Lecture Notes in Computer Science, Springer, 2011, pp. 11–46, Section 3.5, Claim 2 and its proof; Section 3.1 (Shamir's scheme).
