# Rushby's unwinding conditions imply TA-security

Call a family $\{\sim_u\}_{u \in D}$ of equivalence relations on the states of a system $M$ with observations, as in [TA-security](ta-security.md), a *weak unwinding* for
$\rightsquigarrow$ if it satisfies

- (OC) $s \sim_u t$ implies $\mathrm{obs}_u(s) = \mathrm{obs}_u(t)$;
- (WSC) $s \sim_u t$ and $s \sim_{\mathrm{dom}(a)} t$ imply $s \cdot a \sim_u t \cdot a$;
- (LR) $\mathrm{dom}(a) \not\rightsquigarrow u$ implies $s \sim_u s \cdot a$.

**Theorem (van der Meyden).** If there is a weak unwinding for $M$ with respect to $\rightsquigarrow$, then $M$ is TA-secure with respect to $\rightsquigarrow$.

Since TA-security is strictly stronger than IP-security, the existence of a weak unwinding is not necessary for IP-security, which explains why Rushby's unwinding
conditions are sound but not complete for it.

## Depends on

- [TA-security for intransitive policies](ta-security.md)

## Sources

- R. van der Meyden, "What, indeed, is intransitive noninterference? (Preliminary report)", School of Computer Science and Engineering, University of New South Wales, <https://cgi.cse.unsw.edu.au/~meyden/research/rw2.pdf>: Section 4, the conditions OC, WSC and LR, Proposition 5 and Theorem 2 with its proof.
