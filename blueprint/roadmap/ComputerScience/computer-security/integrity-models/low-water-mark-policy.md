# Biba's low-water mark policy

Let a system have subjects, objects and the access relations of [integrity levels and information transfer paths](integrity-levels-and-information-transfer-paths.md),
where the integrity levels form a lattice with meet $\min$. In the *low-water mark policy* the integrity level of a subject changes with its behaviour, while the
levels of objects are fixed:

- (A3.1) after each observe access by a subject $s$ to an object $o$, the level of $s$ becomes $il'(s) = \min(il(s), il(o))$, where $il(s)$ is its level just before the access;
- (A3.2) $s \,\underline{m}\, o \implies il(o) \le il(s)$;
- (A3.3) $s_1 \,\underline{i}\, s_2 \implies il(s_2) \le il(s_1)$.

The level of each subject is therefore nonincreasing and equals the low-water mark of the integrity levels of the objects it has observed (and its initial level).

## Depends on

- [Integrity levels and information transfer paths](integrity-levels-and-information-transfer-paths.md)

## Sources

- K. J. Biba, *Integrity Considerations for Secure Computer Systems*, Technical Report ESD-TR-76-372 (MITRE MTR-3153, Rev. 1), The MITRE Corporation, April 1977, DTIC accession number AD-A039324: Section III, "The Low-Water Mark Policy" (axioms A3.1–A3.3 and Figure 5).
