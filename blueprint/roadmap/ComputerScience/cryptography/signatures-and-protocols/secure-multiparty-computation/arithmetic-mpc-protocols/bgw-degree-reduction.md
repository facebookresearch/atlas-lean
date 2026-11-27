# BGW degree reduction and gate privacy

Let $\mathbb{F}$ be a finite field, $m$ parties with distinct nonzero evaluation points $\alpha_1, \dots, \alpha_m$, and threshold $t$ with $2t < m$. (i) *Multiplicativity:* if $f, g$ are degree-$t$ sharing polynomials of $a$ and $b$, then $fg$ has degree $2t$ and constant term $ab$, so Lagrange reconstruction from the products $f(\alpha_i)g(\alpha_i)$ of shares returns $ab$. (ii) *Degree reduction:* if every party $j$ reshares its product share $h(\alpha_j)$ with a fresh degree-$t$ Shamir polynomial and every party $i$ computes $\sum_j \lambda_j\, \mathrm{share}_{j \to i}$ with the Lagrange weights $\lambda_j$ at zero, the results are a degree-$t$ Shamir sharing of $ab$ (Lagrange reconstruction commutes with Shamir sharing). (iii) *Privacy:* for every coalition $I$ with $|I| \le t$, the joint view of $I$ in the degree-reduction protocol, and the joint view and outputs of the BGW addition and multiplication gate protocols, are perfectly simulatable from the coalition's inputs and outputs.

## Proof sketch

(i) and (ii) are linearity of Lagrange interpolation and of Shamir sharing. (iii) The reshared values seen by $I$ are at most $t$ shares of each fresh polynomial, which are uniform by marginal uniformity of Shamir shares.

## Depends on

- [Shamir threshold secret sharing](../secret-sharing-schemes/shamir-secret-sharing.md)
- [Synchronous oracle-aided multiparty protocols and perfect semi-honest privacy](../semi-honest-mpc-foundations/oracle-aided-protocols-and-perfect-privacy.md)
- [Security of the BGW protocol against semi-honest adversaries](../security-of-the-bgw-protocol-against-semi.md)

## Proof depends on

- [Linearity, multiplicativity and privacy of Shamir sharing](../secret-sharing-schemes/shamir-sharing-properties.md)

## Sources

- Michael Ben-Or, Shafi Goldwasser and Avi Wigderson, "Completeness Theorems for Non-Cryptographic Fault-Tolerant Distributed Computation", Proceedings of the Twentieth Annual ACM Symposium on Theory of Computing, 1988.
- Rosario Gennaro, Michael O. Rabin and Tal Rabin, "Simplified VSS and Fast-Track Multiparty Computations with Applications to Threshold Cryptography", Proceedings of the Seventeenth Annual ACM Symposium on Principles of Distributed Computing, 1998.
- Gilad Asharov and Yehuda Lindell, "A Full Proof of the BGW Protocol for Perfectly Secure Multiparty Computation", Journal of Cryptology, 2017.
