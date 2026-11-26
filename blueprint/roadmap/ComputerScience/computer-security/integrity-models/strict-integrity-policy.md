# Biba's strict integrity policy

Let a system have subjects, objects, integrity levels and the access relations observe $\underline{o}$, modify $\underline{m}$ and invoke $\underline{i}$ as in
[integrity levels and information transfer paths](integrity-levels-and-information-transfer-paths.md). The *strict integrity policy* consists of the axioms

- (A3.6) $s \,\underline{o}\, o \implies il(s) \le il(o)$: a subject observes only objects of integrity at least its own;
- (A3.7) $s \,\underline{m}\, o \implies il(o) \le il(s)$: a subject modifies only objects of integrity at most its own;
- (A3.8) $s_1 \,\underline{i}\, s_2 \implies il(s_2) \le il(s_1)$: a subject invokes only subjects of integrity at most its own,

for all subjects $s, s_1, s_2$ and objects $o$. The first two axioms are the duals of the simple security condition and the $*$-property of the
[Bell–LaPadula model](../access-control/basic-security-theorem-of-bell-and-lapadula.md): no read down and no write up.

## Depends on

- [Integrity levels and information transfer paths](integrity-levels-and-information-transfer-paths.md)

## Sources

- K. J. Biba, *Integrity Considerations for Secure Computer Systems*, Technical Report ESD-TR-76-372 (MITRE MTR-3153, Rev. 1), The MITRE Corporation, April 1977, DTIC accession number AD-A039324: Section III, "The Strict Integrity Policy" (axioms A3.6–A3.8 and Figure 7).
