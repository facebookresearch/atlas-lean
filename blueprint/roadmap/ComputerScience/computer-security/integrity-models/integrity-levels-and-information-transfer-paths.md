# Integrity levels and information transfer paths

In Biba's model a system has a set $S$ of subjects, a set $O$ of objects and a set $I$ of *integrity levels* partially ordered by $\le$, with a function $il$ giving
each subject and object its integrity level; a higher level means more trustworthy information. Access is described by three relations: *observe*
$\underline{o} \subseteq S \times O$, *modify* $\underline{m} \subseteq S \times O$ and *invoke* $\underline{i} \subseteq S \times S$ (a request for service from one subject to
another, a special case of modification).

An *information transfer path* from an object $o_1$ to an object $o_{n+1}$ is a sequence of objects $o_1, \dots, o_{n+1}$ together with a sequence of subjects
$s_1, \dots, s_n$ such that $s_i \,\underline{o}\, o_i$ and $s_i \,\underline{m}\, o_{i+1}$ for every $1 \le i \le n$: each subject observes one object and modifies the next.

## Sources

- K. J. Biba, *Integrity Considerations for Secure Computer Systems*, Technical Report ESD-TR-76-372 (MITRE MTR-3153, Rev. 1), The MITRE Corporation, April 1977, DTIC accession number AD-A039324: Section III, "Mandatory integrity policy" (the elements of policy and the access modes observe, modify and invoke) and Definition D3.1 (information transfer path).
