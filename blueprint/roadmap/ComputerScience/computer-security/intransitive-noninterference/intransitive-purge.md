# Sources and intransitive purge

Let $A$ be a set of actions, each with a domain $\mathrm{dom}(a)$ in a set $D$ of security domains, and let $\rightsquigarrow$ be a policy, a reflexive relation on $D$
that need not be transitive. The function $\mathrm{sources} : A^* \times D \to \mathcal P(D)$ is defined by right recursion:
$$\mathrm{sources}(\Lambda, u) = \{u\}, \qquad
\mathrm{sources}(a \circ \alpha, u) = \begin{cases} \mathrm{sources}(\alpha, u) \cup \{\mathrm{dom}(a)\} & \text{if } \mathrm{dom}(a) \rightsquigarrow v \text{ for some } v \in \mathrm{sources}(\alpha, u),\\ \mathrm{sources}(\alpha, u) & \text{otherwise,}\end{cases}$$
where $\Lambda$ is the empty sequence and $a \circ \alpha$ prefixes the action $a$ to $\alpha$. Thus $v \in \mathrm{sources}(\alpha, u)$ when $v = u$ or $\alpha$ has a subsequence of
actions of domains $w_1 \rightsquigarrow w_2 \rightsquigarrow \cdots \rightsquigarrow w_n$ with $w_1 = v$ and $w_n = u$. The *intransitive purge* $\mathrm{ipurge} : A^* \times D \to A^*$ is
$$\mathrm{ipurge}(\Lambda, u) = \Lambda, \qquad
\mathrm{ipurge}(a \circ \alpha, u) = \begin{cases} a \circ \mathrm{ipurge}(\alpha, u) & \text{if } \mathrm{dom}(a) \in \mathrm{sources}(a \circ \alpha, u),\\ \mathrm{ipurge}(\alpha, u) & \text{otherwise:}\end{cases}$$
it deletes from $\alpha$ the actions that should not be able to interfere with $u$. When $\rightsquigarrow$ is transitive, $\mathrm{ipurge}(\alpha, u)$ is the ordinary purge,
which deletes the actions $a$ with $\mathrm{dom}(a) \not\rightsquigarrow u$.

## Sources

- J. Rushby, *Noninterference, transitivity, and channel-control security policies*, Technical Report CSL-92-02, SRI International, 1992, <http://www.csl.sri.com/papers/csl-92-2/csl-92-2.pdf>: Chapter 4, Definition 8 (the functions sources and ipurge).
- R. van der Meyden, "What, indeed, is intransitive noninterference? (Preliminary report)", School of Computer Science and Engineering, University of New South Wales, <https://cgi.cse.unsw.edu.au/~meyden/research/rw2.pdf>: Section 2 (the right-to-left formulation of ipurge and its agreement with purge for transitive policies).
