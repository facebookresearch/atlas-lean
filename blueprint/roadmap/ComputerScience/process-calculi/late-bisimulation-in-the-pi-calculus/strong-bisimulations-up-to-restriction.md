# Strong bisimulations up to restriction are contained in strong late bisimilarity

In the [late transition semantics](late-transition-semantics-of-the-pi-calculus.md), a binary relation $\mathcal{S}$ on agents is a *strong simulation up to restriction* if $P \mathcal{S} Q$ implies:

1. if $w \notin \mathrm{fn}(P, Q)$, then $P\{w/z\} \mathcal{S} Q\{w/z\}$ for every name $z$;
2. if $P \xrightarrow{\alpha} P'$ with $\alpha$ a free output, then $Q \xrightarrow{\alpha} Q'$ and $P' \mathcal{S} Q'$ for some $Q'$;
3. if $P \xrightarrow{x(y)} P'$ and $y \notin \mathrm{n}(P, Q)$, then $Q \xrightarrow{x(y)} Q'$ for some $Q'$ such that $P'\{v/y\} \mathcal{S} Q'\{v/y\}$ for every name $v$;
4. if $P \xrightarrow{\bar x(y)} P'$ and $y \notin \mathrm{n}(P, Q)$, then $Q \xrightarrow{\bar x(y)} Q'$ and $P' \mathcal{S} Q'$ for some $Q'$;
5. if $P \xrightarrow{\tau} P'$, then $Q \xrightarrow{\tau} Q'$ for some $Q'$ such that either $P' \mathcal{S} Q'$, or $P' = (w) P''$ and $Q' = (w) Q''$ with $P'' \mathcal{S} Q''$ for some $w$, $P''$ and $Q''$.

$\mathcal{S}$ is a *strong bisimulation up to restriction* if both $\mathcal{S}$ and its inverse are strong simulations up to restriction. Every strong bisimulation up to restriction is contained in [strong late bisimilarity](strong-late-bisimilarity.md) $\dot\sim$; the proof shows that the union over $n$ of $\mathcal{S}_0 = \mathcal{S}$ and $\mathcal{S}_{n+1} = \{((w) P, (w) Q) \mid P \mathcal{S}_n Q\}$ is a strong bisimulation.

## Depends on

- [Strong late bisimilarity](strong-late-bisimilarity.md)
- [Late transition semantics of the π-calculus](late-transition-semantics-of-the-pi-calculus.md)

## Sources

- R. Milner, J. Parrow and D. Walker, "A calculus of mobile processes, II", *Information and Computation* 100(1):41–77, 1992, <https://www.pure.ed.ac.uk/ws/files/16426068/A_Calculus_of_Mobile_Processes_II.pdf>, Section 3.2: Definition 15 and Lemma 7; the proof is in the Appendix.
