# Strict integrity confines information transfer to lower integrity

**Theorem.** In a system that enforces the [strict integrity policy](strict-integrity-policy.md), if there is an
[information transfer path](integrity-levels-and-information-transfer-paths.md) from an object $o_1$ to an object $o_{n+1}$, then $il(o_{n+1}) \le il(o_1)$.

For each step of the path, axioms A3.6 and A3.7 give $il(o_{i+1}) \le il(s_i) \le il(o_i)$, and transitivity of $\le$ gives the claim. Thus no information can flow from
an object of low integrity to one of higher (or incomparable) integrity.

## Depends on

- [Biba's strict integrity policy](strict-integrity-policy.md)

## Sources

- K. J. Biba, *Integrity Considerations for Secure Computer Systems*, Technical Report ESD-TR-76-372 (MITRE MTR-3153, Rev. 1), The MITRE Corporation, April 1977, DTIC accession number AD-A039324: Section III, "The Strict Integrity Policy", theorem T3.2 and its proof.
