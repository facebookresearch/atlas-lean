# Indirect invasions destabilize every equilibrium of the repeated prisoner's dilemma

**Setting.** Two players repeat a prisoner's dilemma with actions $C$ (cooperate) and $D$ (defect); after each round the game continues with probability $\delta \in (0,1)$, and payoffs are discounted accordingly. A strategy $S$ maps histories to actions; $\pi(S', S)$ is the expected payoff of $S'$ against $S$. In a large population playing $S$, a mutant $S'$ is

- *unable to invade* if $\pi(S', S) < \pi(S, S)$, or $\pi(S', S) = \pi(S, S)$ and $\pi(S', S') < \pi(S, S')$;
- a *neutral mutant* if $\pi(S', S) = \pi(S, S)$ and $\pi(S', S') = \pi(S, S')$.

$S$ is a Nash equilibrium if $\pi(S', S) \le \pi(S, S)$ for all $S'$; an *evolutionarily stable strategy* (ESS) if no mutant can invade; *neutrally stable* (NSS) if every mutant either cannot invade or is neutral; and *robust against indirect invasions* (RAII) if it is an NSS and no chain of neutral mutants opens the door to a strategy that can then invade. These satisfy $\mathrm{ESS} \subseteq \mathrm{RAII} \subseteq \mathrm{NSS} \subseteq \text{Nash}$.

**Results.** In the repeated prisoner's dilemma with sufficiently many expected repetitions:

1. No strategy is an ESS.
2. No strategy is RAII: from every Nash equilibrium there is a path out, a sequence of neutral mutants after which a strategy that could not invade the original population can invade.
3. There are infinitely many Nash equilibria and NSSs, with different levels of cooperation.

**Example.** Tit-for-tat (TFT) is a Nash equilibrium for $\delta$ large enough but not an ESS: always-cooperate (ALLC) earns exactly what TFT earns against TFT and against ALLC, so it drifts in neutrally. Once ALLC is sufficiently frequent, always-defect (ALLD), which cannot invade pure TFT, invades by exploiting ALLC.

## Expansion

Against any strategy, a mutant that differs only off the equilibrium path (in histories never reached when the resident plays itself) is neutral. Such drift can remove the punishment that kept a defector out, which is the indirect invasion; conversely, defecting populations can be indirectly invaded by cooperative strategies. Evolution in an unrestricted strategy space therefore moves between equilibria, and long-run cooperation levels are set by the mutation (exploration) process rather than by any single stable strategy.

## Sources

- J. García and M. van Veelen, "No Strategy Can Win in the Repeated Prisoner's Dilemma: Linking Game Theory and Computer Simulations", *Frontiers in Robotics and AI* 5 (2018) 102, Sections 2–3 (Nash equilibrium and its refinements, indirect invasions, Figure 1) and Section 5.1 (paths out of equilibrium). <https://doi.org/10.3389/frobt.2018.00102> (PMC7805755)
