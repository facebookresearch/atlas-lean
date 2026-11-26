# Reducing randomized functionalities to deterministic ones

Let $f$ be an $m$-party randomized functionality $f(x; \rho)$. Define the deterministic functionality $g((x_1, \rho_1), \dots, (x_m, \rho_m)) = f(x; \rho_1 \oplus \dots \oplus \rho_m)$. If a protocol privately computes $g$ against coalitions of at most $t < m$ parties, then the protocol in which every party samples its own uniform $\rho_i$ and runs the protocol for $g$ privately computes $f$ against the same coalitions: the coins $\rho = \bigoplus_i \rho_i$ are uniform and independent of every proper coalition's view. In the oracle-hybrid setting, a randomized wrapper of this kind is perfectly private whenever the deterministic protocol is.

## Proof sketch

For any proper coalition, the XOR of the honest parties' coins is uniform and independent, so the coalition's ideal view for $g$ with its own coins is distributed as its ideal view for $f$.

## Depends on

- [Synchronous oracle-aided multiparty protocols and perfect semi-honest privacy](oracle-aided-protocols-and-perfect-privacy.md)

## Sources

- Oded Goldreich, "Foundations of Cryptography, Volume 2: Basic Applications", Cambridge University Press, 2004.
