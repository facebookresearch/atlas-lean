# Alpha-convertible agents are strongly late bisimilar

In the [late transition semantics](late-transition-semantics-of-the-pi-calculus.md), alpha-convertibility $\equiv_\alpha$ is a strong bisimulation, so alpha-convertible agents are related by [strong late bisimilarity](strong-late-bisimilarity.md) $\dot\sim$. The key step: if $P \equiv_\alpha Q$ and $P \xrightarrow{\alpha} P'$ with $\alpha$ free, then $Q \xrightarrow{\alpha} Q'$ for some $Q' \equiv_\alpha P'$; and if $P \xrightarrow{\alpha} P'$ with bound object $y$ and $z \notin \mathrm{n}(Q)$, then $Q$ has the same transition with object $z$ to some $Q' \equiv_\alpha P'\{z/y\}$.

## Depends on

- [Strong late bisimilarity](strong-late-bisimilarity.md)
- [Late transition semantics of the π-calculus](late-transition-semantics-of-the-pi-calculus.md)

## Sources

- R. Milner, J. Parrow and D. Walker, "A calculus of mobile processes, II", *Information and Computation* 100(1):41–77, 1992, <https://www.pure.ed.ac.uk/ws/files/16426068/A_Calculus_of_Mobile_Processes_II.pdf>, Section 3.1: Lemma 5 and Theorem 1, after which alpha-convertible agents are identified.
