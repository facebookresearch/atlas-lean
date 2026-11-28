# Risk-dominance condition for tag-based cooperation

**Model.** A well-mixed population of $N$ individuals carries one of $K \ge 2$ tags and one of two behaviours, so there are $2K$ phenotypes $C_1, D_1, \dots, C_K, D_K$. A cooperator $C_i$ pays a cost $c > 0$ to give a benefit $b > c$ to every individual carrying the same tag $i$; defectors never help, and nobody helps an individual with a different tag. Strategies spread by pairwise comparison: two individuals are drawn at random and the first copies the second with probability $(1 + e^{-\beta(\pi_2 - \pi_1)})^{-1}$, where $\pi_1, \pi_2$ are their payoffs and $\beta \ge 0$ is the intensity of selection. With a small probability an individual mutates. Write $u_C, u_D$ for the rates of mutations that change only the strategy (from a cooperator, respectively from a defector, keeping the tag) and $v_C, v_D$ for the rates of mutations that change both strategy and tag.

**Statement** (Traulsen and Nowak 2007, eqs. (1)–(8)). In the limit of rare mutations the population is almost always homogeneous, and its dynamics is a Markov chain on the $2K$ homogeneous states with four kinds of transition, $C_i \to D_i$, $C_i \to D_j$, $D_i \to C_i$ and $D_i \to C_j$ ($j \ne i$), each with rate equal to a mutation rate times $N$ times the fixation probability of the mutant. Cooperator states are occupied more often than defector states exactly when the total rate into cooperator states exceeds the total rate out of them (eq. (2)). Assume weak selection, $\beta \ll 1/N$, and symmetric mutation, $u_C = u_D = u$ and $v_C = v_D = v$ with $u, v > 0$. Then for large $N$ cooperators have the higher average abundance if and only if

$$\frac{b}{c} > 1 + \frac{2u}{v}.$$

Without the symmetry assumption the selection terms are swamped at $\beta \to 0$ by any asymmetry of the mutation rates, which then alone decides which behaviour is more abundant (eq. (4)); the symmetry condition removes this effect.

## Proof depends on

- [Rare-mutation limit of the pairwise comparison process](../stochastic-games-with-environmental-feedback/rare-mutation-limit-of-the-pairwise-comparison-process.md)

## Proof sketch

There are two kinds of contest between a resident and a mutant. If cooperators and defectors share a tag they play the Prisoner's Dilemma with payoff matrix (rows cooperator, defector; columns cooperator, defector)

$$\begin{pmatrix} b - c & -c \\ b & 0 \end{pmatrix},$$

and if their tags differ they play

$$\begin{pmatrix} b - c & 0 \\ 0 & 0 \end{pmatrix},$$

because a cooperator then helps only its own kind (eqs. (12)–(13)). For weak selection and large $N$ the fixation probability of a single mutant of type $A$ in a resident population of type $B$ exceeds the reverse one exactly when $A$ is risk dominant, which for a $2 \times 2$ game means that the first-row sum of the payoff matrix exceeds the second-row sum; this is the large-$N$ form of the weak-selection fixation formula behind the one-third rule (eq. (19)). Same-tag transitions occur at rate proportional to $u$ and different-tag transitions at rate proportional to $v$, so the weighted matrix $u M_{\text{same}} + v M_{\text{diff}}$ governs the comparison. Its first-row sum is $u(b - 2c) + v(b - c)$ and its second-row sum is $ub$; the first exceeds the second iff $v(b - c) > 2uc$, which is the displayed condition. Cooperation survives because a defector invading with the same tag destroys cooperation only for that tag, while a cooperator mutating to a fresh tag starts a new cooperative cluster that defectors must rediscover.

## Sources

- A. Traulsen and M. A. Nowak, "Chromodynamics of cooperation in finite populations", PLoS ONE 2 (2007), e270, Results and Discussion, eqs. (1)–(8) and (12)–(14), and Materials and Methods, eqs. (15)–(19), <https://doi.org/10.1371/journal.pone.0000270>, PMCID PMC1803018.
