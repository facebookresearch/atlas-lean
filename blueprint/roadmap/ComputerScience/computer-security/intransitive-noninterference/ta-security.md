# TA-security for intransitive policies

Consider systems $M = \langle S, s_0, \mathrm{step}, \mathrm{obs}, \mathrm{dom} \rangle$ with actions $A$, where $s \cdot \alpha$ is the state reached from $s$ by the action
sequence $\alpha$, $\mathrm{obs}_u(s)$ is the observation of domain $u$ in state $s$ and $\mathrm{dom}(a)$ is the domain of action $a$, and let $\rightsquigarrow$ be a
reflexive policy on domains. $M$ is *IP-secure* for $\rightsquigarrow$ if $\mathrm{obs}_u(s_0 \cdot \alpha) = \mathrm{obs}_u(s_0 \cdot \mathrm{ipurge}(\alpha, u))$ for every domain
$u$ and sequence $\alpha$, where $\mathrm{ipurge}$ is the [intransitive purge](intransitive-purge.md).

Let $HT(A^*)$ be the smallest set containing $A^*$ and closed under forming triples $(x, y, z)$. For each domain $u$ define $\mathrm{ta}_u : A^* \to HT(A^*)$ by
$\mathrm{ta}_u(\epsilon) = \epsilon$ and, for $\alpha \in A^*$ and $a \in A$,
$$\mathrm{ta}_u(\alpha a) = \begin{cases} \mathrm{ta}_u(\alpha) & \text{if } \mathrm{dom}(a) \not\rightsquigarrow u,\\ (\mathrm{ta}_u(\alpha), \mathrm{ta}_{\mathrm{dom}(a)}(\alpha), a) & \text{if } \mathrm{dom}(a) \rightsquigarrow u.\end{cases}$$
$\mathrm{ta}_u(\alpha)$ is the most information that the policy allows $u$ to have about the actions in $\alpha$: an interfering action may transmit everything its own
domain may know, together with the fact that it was performed. $M$ is *TA-secure* for $\rightsquigarrow$ if $\mathrm{ta}_u(\alpha) = \mathrm{ta}_u(\alpha')$ implies
$\mathrm{obs}_u(s_0 \cdot \alpha) = \mathrm{obs}_u(s_0 \cdot \alpha')$ for all domains $u$ and all $\alpha, \alpha' \in A^*$.

## Depends on

- [Sources and intransitive purge](intransitive-purge.md)

## Sources

- R. van der Meyden, "What, indeed, is intransitive noninterference? (Preliminary report)", School of Computer Science and Engineering, University of New South Wales, <https://cgi.cse.unsw.edu.au/~meyden/research/rw2.pdf>: Section 2 (systems with observations and IP-security) and Section 3 (the functions $\mathrm{ta}_u$ and the definition of TA-security).
