# Elimination of non-interacting species by fast reactions

**Setting.** A stochastic reaction network on species $\mathcal S = \mathcal S_{\mathrm{core}} \cup \mathcal U$ is a continuous-time Markov chain on $\mathbb Z^{n}_{\ge 0}$ with intensities $\lambda_r$ satisfying $\lambda_r(x) > 0 \iff x \ge y$ for each reaction $r : y \to y'$ (as for mass-action kinetics). A set $\mathcal U$ of $n - p$ species is *non-interacting* if no complex contains two of its species and each appears with coefficient $0$ or $1$; examples are enzyme–substrate complexes and other intermediates. Let a subset $\mathcal R_f$ of the reactions consuming $\mathcal U$ be fast, with intensities scaled by $1/\varepsilon$, giving chains $X_\varepsilon$. Assume $\mathcal R_f$ is *proper* with respect to $\mathcal U$: every species of $\mathcal U$ lies on a *fast chain*, a sequence of reactions $y_0\to y_0', y_1\to y_1',\dots,y_l\to y_l'$, the first producing $\mathcal U$ from a $\mathcal U$-free complex and the others fast, with $y_0$ and $y_l'$ free of $\mathcal U$ and the $\mathcal U$-part of $y_j$ equal to that of $y_{j-1}'\ne0$ for $j\ge1$. The *reduced network* on the core species replaces each walk through $\mathcal U$ (a sequence of fast reactions entering and leaving $\mathcal U$) by a single reaction whose intensity $\Lambda_w$ is the entry rate times the probability of that exit route.

**Theorem.**

1. *(Convergence.)* Suppose the relevant closed class $E$ is finite and no fast walk is blocked or leaks (the summed walk intensities $\Lambda_w(z)$ equal the slow intensities leaving through $\mathcal U$, for all core states $z$). Then for initial laws $\pi$ supported on states with no $\mathcal U$-molecules and every $T > 0$,

    $$\sup_{t \in [0, T]}\bigl|P_\pi(X_\varepsilon(t) \in B) - P_{\pi_0}(X_0(t) \in B_0)\bigr| = O(\varepsilon) \quad (\varepsilon \to 0),$$

    where $X_0$ is the reduced network's chain and $\pi_0, B_0$ are projections to core coordinates.

2. *(Intermediates preserve recurrence.)* If $\mathcal U$ consists of intermediate species (every complex containing a species of $\mathcal U$ is a single molecule of that species), $\mathcal R_f$ is the set of all reactions with a $\mathcal U$-species in the reactant, and the network is sub-conservative, then a state $(z, 0)$ is transient (resp. positive recurrent) for the full network iff $z$ is transient (resp. positive recurrent) for the reduced network, and irreducible components project onto irreducible components.

## Expansion

Because species in $\mathcal U$ never meet each other and occur singly, a molecule entering $\mathcal U$ performs an absorbing Markov walk through the $\mathcal U$-states driven by fast reactions, with core species frozen on that time scale. Its exit distribution is computable from a linear system, which defines the reduced reactions and rates; a singular-perturbation estimate for finite-state chains with a fast transient part gives the $O(\varepsilon)$ error. Recurrence classification transfers because intermediates are visited for finite, fast excursions, so embedded jump chains of the full and reduced networks agree on core states.

## Sources

- Linard Hoessly and Carsten Wiuf, "Fast reactions with non-interacting species in stochastic reaction networks", Mathematical Biosciences and Engineering 19 (2022), 2720–2749, <https://doi.org/10.3934/mbe.2022124>; numbering as in arXiv:2110.13235: Theorem 4.1, Corollary 4.2 and Theorem 5.10.
