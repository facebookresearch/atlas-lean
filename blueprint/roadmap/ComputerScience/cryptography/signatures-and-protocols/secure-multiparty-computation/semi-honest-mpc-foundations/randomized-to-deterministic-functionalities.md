# Reducing randomized functionalities to deterministic ones

Let $f$ be an $m$-party randomized functionality $f(x; \rho)$. Define the deterministic functionality $g((x_1, \rho_1), \dots, (x_m, \rho_m)) = f(x; \rho_1 \oplus \dots \oplus \rho_m)$. If a protocol privately computes $g$ against coalitions of at most $t < m$ parties, then the protocol in which every party samples its own uniform $\rho_i$ and runs the protocol for $g$ privately computes $f$ against the same coalitions: the combined coins $\rho = \bigoplus_i \rho_i$ are uniform and independent of the coalition's local random coins $\{\rho_i\}_{i \in I}$ (even though $f$'s outputs may depend on $\rho$), so privately computing $g$ reduces $f$ to $g$ (Goldreich, Proposition 7.3.4 and Section 7.5.2.4, Eq. (7.48); Asharov and Lindell, Section 2.1 for the $t$-threshold form). In the oracle-hybrid setting, this randomized reduction is perfectly private.

## Proof sketch

For any proper coalition $I$ of size at most $t < m$, at least one honest party $j \notin I$ contributes a fresh uniform string $\rho_j$, so $\rho = \bigoplus_i \rho_i$ is uniform and independent of $\{\rho_i\}_{i \in I}$ and of the inputs. The simulator for $I$ on input $(x_I, y_I)$ samples fresh uniform $\{\rho_i\}_{i \in I}$ and runs the simulator for $g$ on $((x_I, \rho_I), y_I)$; because $g((x_1, \rho_1), \dots, (x_m, \rho_m)) = f(x; \rho)$ depends on the coin tuple only through $\rho$, the simulated view and outputs are identically distributed to the real execution.

## Depends on

- [Synchronous oracle-aided multiparty protocols and perfect semi-honest privacy](oracle-aided-protocols-and-perfect-privacy.md)

## Sources

- Oded Goldreich, "Foundations of Cryptography, Volume 2: Basic Applications", Cambridge University Press, 2004, Proposition 7.3.4 (privately reducing a two-party randomized functionality to a deterministic one, Eq. (7.19)) and Section 7.5.2.4, Eq. (7.48) ($m$-party analogue).
- Gilad Asharov and Yehuda Lindell, "A Full Proof of the BGW Protocol for Perfectly Secure Multiparty Computation", Journal of Cryptology 30(1), 2017, Section 2.1 ($t$-threshold reduction of randomized functionalities to deterministic ones).
