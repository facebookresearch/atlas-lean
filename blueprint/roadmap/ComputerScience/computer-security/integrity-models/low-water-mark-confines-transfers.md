# The low-water mark policy confines information transfer to lower integrity

**Theorem.** In a system that enforces the [low-water mark policy](low-water-mark-policy.md), suppose that each access is indivisible and mutually exclusive, and
that there is an [information transfer path](integrity-levels-and-information-transfer-paths.md) from an object $o_1$ to an object $o_{n+1}$ all of whose accesses
succeed, each subject $s_i$ first observing $o_i$ and then modifying $o_{i+1}$. Then $il(o_{n+1}) \le il(o_1)$.

After $s_i$ observes $o_i$ its level is at most $il(o_i)$ by A3.1, so the modification allowed by A3.2 gives $il(o_{i+1}) \le il(o_i)$; the claim follows by transitivity.

## Depends on

- [Biba's low-water mark policy](low-water-mark-policy.md)

## Sources

- K. J. Biba, *Integrity Considerations for Secure Computer Systems*, Technical Report ESD-TR-76-372 (MITRE MTR-3153, Rev. 1), The MITRE Corporation, April 1977, DTIC accession number AD-A039324: Section III, "The Low-Water Mark Policy", theorem T3.1 and its proof.
