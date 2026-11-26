# TA-security is characterized by weak unwindings of the unfolded system

Given a system $M = \langle S, s_0, \mathrm{step}, \mathrm{obs}, \mathrm{dom} \rangle$ with actions $A$, its *unfolding* $\mathrm{uf}(M)$ has the same actions and domains, states
$A^*$, initial state $\epsilon$, transitions $\mathrm{step}'(\alpha, a) = \alpha a$ and observations $\mathrm{obs}'_u(\alpha) = \mathrm{obs}_u(s_0 \cdot \alpha)$.

**Theorem (van der Meyden).** $M$ is [TA-secure](ta-security.md) with respect to $\rightsquigarrow$ if and only if there is a
[weak unwinding](weak-unwinding-implies-ta-security.md) on $\mathrm{uf}(M)$ with respect to $\rightsquigarrow$.

The existence of a weak unwinding on $M$ itself is not invariant under bisimulation, which is why the characterization passes through the unfolding.

## Depends on

- [TA-security for intransitive policies](ta-security.md)
- [Rushby's unwinding conditions imply TA-security](weak-unwinding-implies-ta-security.md)

## Sources

- R. van der Meyden, "What, indeed, is intransitive noninterference? (Preliminary report)", School of Computer Science and Engineering, University of New South Wales, <https://cgi.cse.unsw.edu.au/~meyden/research/rw2.pdf>: Section 4, the unfolding $\mathrm{uf}(M)$ and Theorem 3 with its proof.
