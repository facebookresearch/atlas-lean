# TA-security implies IP-security, strictly

**Theorem (van der Meyden).** For every system $M$ and policy $\rightsquigarrow$, if $M$ is [TA-secure](ta-security.md) for $\rightsquigarrow$ then $M$ is IP-secure for
$\rightsquigarrow$. The converse fails: there is a system with domains $H_1, H_2, D_1, D_2, L$ and the policy $H_i \rightsquigarrow D_i \rightsquigarrow L$ ($i = 1, 2$), in which each domain
observes its intransitive purge of the actions performed, that is IP-secure but not TA-secure. For transitive policies the two notions coincide with purge-based
noninterference.

The first part follows from $\mathrm{ta}_u(\alpha) = \mathrm{ta}_u(\mathrm{ipurge}(\alpha, u))$, proved by induction on $\alpha$.

## Depends on

- [TA-security for intransitive policies](ta-security.md)

## Sources

- R. van der Meyden, "What, indeed, is intransitive noninterference? (Preliminary report)", School of Computer Science and Engineering, University of New South Wales, <https://cgi.cse.unsw.edu.au/~meyden/research/rw2.pdf>: Section 2, Example 1 (the downgrading system), and Section 3, Example 2 and Theorem 1, parts (3) and (4), with the proof of part (3).
