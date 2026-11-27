# Segment duration distributions in hidden Markov models

**Setting.** In a hidden Markov model, a state $s$ with self-transition probability $1 - p$ ($0 < p < 1$) produces segments whose duration $D_s$ (number of consecutive positions spent in $s$) is geometric:

$$\Pr(D_s = d) = p(1 - p)^{d - 1}, \qquad d = 1, 2, \dots,$$

with mode $1$, mean $1/p$, and positive probability for arbitrarily long segments. Biological segments such as transmembrane helices have length distributions concentrated on a finite window (roughly 15–30 residues), which a single geometric state cannot represent.

**Constructions.**

1. *Ladder (chain) of non-self-looping states.* $D_{\max}$ states traversed in order, with skip transitions, represent any distribution on $\{1, \dots, D_{\max}\}$: if from the entry point the chain jumps to the state $d$ steps from its end with probability $w_d$, then $\Pr(D = d) = w_d$.
2. *Chain of $r$ self-looping states* with common exit probability $p$: the duration is a sum of $r$ independent geometrics, a negative binomial,

$$\Pr(D = d) = \binom{d-1}{r-1} p^{r}(1 - p)^{d - r}, \qquad d \ge r,$$

with mean $r/p$ and mode at least $r$.
3. *Explicit duration variables (dynamic Bayesian network or hidden semi-Markov model).* A duration counter variable is sampled on entry to a state from a fixed duration $D$, from an arbitrary distribution on a window $[D_{\min}, D_{\max}]$, or from a geometric law, and decremented each position; the state is held until the counter reaches zero.

**Proposition.** Constructions 1 and 3 represent every distribution with finite support $\{1, \dots, D_{\max}\}$ exactly; construction 2 represents only negative-binomial laws, which have unbounded support. Explicit duration variables reach the same expressiveness as a ladder of $D_{\max}$ states with $O(D_{\max})$ duration parameters but without enlarging the state-transition graph.

## Expansion

The geometric law is the first-passage time of a Bernoulli exit trial at each position. In the ladder, every path through the chain has a deterministic length fixed by the skip taken, so the duration law equals the skip distribution. A sum of $r$ independent $\mathrm{Geometric}(p)$ variables is negative binomial, and its support starts at $r$. In the explicit-duration construction, conditional on entry, the state persists for exactly the sampled number of positions, so any finite-support law is realized; inference cost grows with $D_{\max}$, as for the ladder. Topology predictors use geometric states for loops of unconstrained length and finite-window durations for membrane helices and signal-peptide regions.

## Sources

- Reynolds SM, Käll L, Riffle ME, Bilmes JA, Noble WS, "Transmembrane topology and signal peptide prediction using dynamic bayesian networks" (2008), Background, "Duration modeling", <https://doi.org/10.1371/journal.pcbi.1000213>, PMCID PMC2570248.
- L. R. Rabiner, "A tutorial on hidden Markov models and selected applications in speech recognition", Proceedings of the IEEE 77 (1989) 257–286, <https://doi.org/10.1109/5.18626>.
