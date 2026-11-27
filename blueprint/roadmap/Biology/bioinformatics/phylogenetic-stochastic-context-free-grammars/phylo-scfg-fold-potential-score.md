# Phylogenetic SCFG and the fold potential score

Let $x$ be a multiple alignment of $m$ homologous sequences with columns $x^{(1)}, \dots, x^{(L)}$, related by a rooted phylogenetic tree $T$ with branch lengths. A **phylogenetic stochastic context-free grammar** (phylo-SCFG) is an SCFG whose derivations generate a secondary structure $\sigma$ on positions $1, \dots, L$ (a set of non-crossing base pairs), together with emissions in which

- each unpaired column $x^{(i)}$ is emitted with probability $P\bigl(x^{(i)} \mid T, Q_1\bigr)$ under a single-nucleotide substitution model $Q_1$ on $4$ states, and
- each paired column pair $\bigl(x^{(i)}, x^{(j)}\bigr)$, $(i, j) \in \sigma$, is emitted jointly with probability $P\bigl(x^{(i)}, x^{(j)} \mid T, Q_2\bigr)$ under a di-nucleotide substitution model $Q_2$ on $16$ states that favors compensatory substitutions preserving base pairing,

each column probability being the likelihood of the leaf states on $T$ under the corresponding continuous-time Markov model. Then

$$P(x, \sigma \mid \phi) = P(\sigma \mid \phi) \prod_{i \text{ unpaired}} P\bigl(x^{(i)} \mid T, Q_1\bigr) \prod_{(i,j) \in \sigma} P\bigl(x^{(i)}, x^{(j)} \mid T, Q_2\bigr),$$

and $P(x \mid \phi) = \sum_\sigma P(x, \sigma \mid \phi)$.

**EvoFold.** Use two phylo-SCFGs over the same nucleotide composition: an fRNA model $\phi_{\mathrm{fRNA}}$ with a structural component (folds whose first and last bases pair, emitting from $Q_1$ and $Q_2$) and a non-structural component (emitting from $Q_1$ only), and a background model $\phi_{\mathrm{bg}}$ consisting of the non-structural component alone. The predicted structure is the most probable one, $\hat\sigma = \arg\max_\sigma P(x, \sigma \mid \phi_{\mathrm{fRNA}})$, which may be empty, and the **fold potential score** is the log-likelihood ratio

$$\mathrm{fps}(x) = \log \frac{P(x \mid \phi_{\mathrm{fRNA}})}{P(x \mid \phi_{\mathrm{bg}})},$$

normalized by length when ranking candidates.

## Depends on

- [RNA secondary structure](../nussinov-algorithm-for-rna-secondary-structure/is-structure.md)
- [Site likelihood of a phylogenetic tree](../../phylogenetics/felsenstein-s-pruning-algorithm/likelihood.md)

## Expansion

Column likelihoods are computed by Felsenstein pruning on $T$, once with the $4$-state model per column and once with the $16$-state model per candidate pair, so the grammar sees only one emission probability per column or column pair. The inside algorithm then sums $P(x, \sigma \mid \phi)$ over all structures in $O(L^3)$ time, giving $P(x \mid \phi)$ for both models, and the CYK algorithm gives $\hat\sigma$ by maximization instead of summation. Phylo-SCFGs extend phylo-HMMs as SCFGs extend HMMs, and they weight the evidence of each sequence by its position in the tree rather than counting sequences. Covariation, i.e. pairs of columns changing together so as to keep Watson–Crick or G·U pairs, is rewarded by $Q_2$ and drives the fps; matching the background and fRNA nucleotide distributions keeps GC-rich regions from scoring high by composition alone. Applied to conserved elements of a vertebrate genome alignment, the method predicted about 48,000 structures, including new miRNAs, coding-region folds and clover-leaf shaped families.

## Sources

- J. S. Pedersen, G. Bejerano, A. Siepel, K. Rosenbloom, K. Lindblad-Toh, E. S. Lander, J. Kent, W. Miller and D. Haussler, "Identification and classification of conserved RNA secondary structures in the human genome", PLoS Computational Biology (2006), e33, Materials and Methods "EvoFold algorithm", "The phylo-SCFGs" and "Structure and score predictions" (grammar specification in Protocol S1), <https://doi.org/10.1371/journal.pcbi.0020033>, PMCID PMC1440920.
- B. Knudsen and J. Hein, "RNA secondary structure prediction using stochastic context-free grammars and evolutionary history", Bioinformatics 15 (1999), 446–454, <https://doi.org/10.1093/bioinformatics/15.6.446>.
