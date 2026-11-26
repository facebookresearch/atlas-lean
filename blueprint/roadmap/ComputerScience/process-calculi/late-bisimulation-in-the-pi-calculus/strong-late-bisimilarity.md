# Strong late bisimilarity

In the [late transition semantics of the π-calculus](late-transition-semantics-of-the-pi-calculus.md), a binary relation $\mathcal{S}$ on agents is a *strong simulation* if $P \mathcal{S} Q$ implies:

1. if $P \xrightarrow{\alpha} P'$ and $\alpha$ is a free action ($\tau$ or a free output), then $Q \xrightarrow{\alpha} Q'$ and $P' \mathcal{S} Q'$ for some $Q'$;
2. if $P \xrightarrow{x(y)} P'$ and $y \notin \mathrm{n}(P, Q)$, then $Q \xrightarrow{x(y)} Q'$ for some $Q'$ such that $P'\{w/y\} \mathcal{S} Q'\{w/y\}$ for every name $w$;
3. if $P \xrightarrow{\bar x(y)} P'$ and $y \notin \mathrm{n}(P, Q)$, then $Q \xrightarrow{\bar x(y)} Q'$ and $P' \mathcal{S} Q'$ for some $Q'$.

$\mathcal{S}$ is a *strong bisimulation* if both $\mathcal{S}$ and its inverse are strong simulations, and $P$ and $Q$ are *strongly bisimilar*, $P \mathrel{\dot\sim} Q$, if some strong bisimulation relates them. Strong bisimilarity is itself a strong bisimulation, the largest one.

## Depends on

- [Late transition semantics of the π-calculus](late-transition-semantics-of-the-pi-calculus.md)

## Sources

- R. Milner, J. Parrow and D. Walker, "A calculus of mobile processes, II", *Information and Computation* 100(1):41–77, 1992, <https://www.pure.ed.ac.uk/ws/files/16426068/A_Calculus_of_Mobile_Processes_II.pdf>, Section 2.1: Table 3 (the definition of strong simulation) and Definition 9, with the remark that $\dot\sim$ is the largest bisimulation.
