# Context-dependent trinucleotide substitution rates from a close outgroup

**Setting.** Let the state of an aligned position be its trinucleotide context $a = (A_{i-1}, A_i, A_{i+1})$. Compare three species whose divergence is recent enough that at most one substitution per site is likely on the focal lineage (human, chimpanzee and an outgroup such as baboon), so that the ancestral state and the direction of each substitution can be read off by parsimony, with a correction for the non-parsimonious configurations that arise on the deeper outgroup branch.

**Statement** (Asthana et al. 2007, Methods "Estimation of mutation rates"). Count, over background positions of the alignment, the frequency of every trinucleotide and of every inferred substitution $a \to b$ on the focal lineage, and set $p(a \to b)$ to the corrected per-trinucleotide substitution probability. Define the rate matrix $Q$ on the $64$ trinucleotide states by

$$Q(a, b) = p(a \to b)\ (a \ne b), \qquad Q(a, a) = -\sum_{b \ne a} Q(a, b),$$

so each row sums to zero. If the focal lineage is short enough that double hits at a site are negligible, $Q$ scaled to unit time is the instantaneous rate matrix, and the transition probabilities over an arbitrary branch length $t$ are the matrix exponential

$$P(t) = e^{Qt},$$

computed by a Padé approximation. Insertions and deletions are added as a separate, first-order model: with $N_a$ ancestral bases, $\mathrm{ins}(k)$ insertions and $\mathrm{del}(k)$ deletions of size $k$ observed, the per-window probability of an insertion of size $k$ in a window of $n$ positions is $\mathrm{ins}(k)\, n / N_a$ and the probability of a deletion of size $k$ overlapping that window is $(k + n - 1)\, \mathrm{del}(k) / N_a$; indel probabilities are taken to scale linearly with time, since indels are an order of magnitude rarer than substitutions.

## Remarks

Restricting to closely related genomes trades statistical depth for identifiability: with multiple hits negligible, the transition matrix is a direct count rather than the solution of a likelihood problem in $64 \times 63$ free parameters, which deep-phylogeny estimation would require. A first-order context is enough because higher orders add parameters without measurably changing the fitted rates, while ignoring context entirely misestimates the rates badly — CpG positions alone mutate about an order of magnitude faster than other dinucleotide contexts. The generator form guarantees that $e^{Qt}$ is a stochastic matrix for every $t \ge 0$, so a single counting matrix extends to the branch lengths of a whole mammalian tree.

## Sources

- S. Asthana, M. Roytberg, J. Stamatoyannopoulos and S. Sunyaev, "Analysis of sequence conservation at nucleotide resolution", PLoS Computational Biology 3 (2007), e254, Methods ("Estimation of mutation rates", "Gap model"), <https://doi.org/10.1371/journal.pcbi.0030254>, PMCID PMC2230682.
