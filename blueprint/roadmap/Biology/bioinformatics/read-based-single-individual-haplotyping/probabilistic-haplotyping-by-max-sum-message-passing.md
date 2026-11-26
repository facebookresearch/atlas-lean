# Probabilistic haplotyping by max-sum message passing

**Data.** Let $m$ heterozygous sites and $n$ reads be given by a phasing matrix $M \in \{0, 1, -\}^{n \times m}$ ($M_{ij}$ is the allele read $i$ shows at site $j$, or $-$ if it does not cover $j$) and an error matrix $Q \in [0, 1)^{n \times m}$ of per-base error probabilities. Let $\mathrm{Po}(i) = \{j : M_{ij} \ne -\}$, and let $R_j = \{i : \min \mathrm{Po}(i) \le j \le \max \mathrm{Po}(i)\}$ be the reads spanning site $j$.

**Model.** The hidden variables are a haplotype $h \in \{0, 1\}^m$ (the other haplotype is its complement $\bar h$) and read origins $r \in \{0, 1\}^n$; write $h_j(r_i) = h_j$ if $r_i = 0$ and $\bar h_j$ if $r_i = 1$. The joint law is

$$P(r, h, o) = \prod_{i=1}^{n} \prod_{j \in \mathrm{Po}(i)} P(o_{ij} \mid r_i, h_j) \prod_i P(r_i) \prod_j P(h_j), \qquad P(o_{ij} \mid r_i, h_j) = \begin{cases} 1 - Q_{ij} & o_{ij} = h_j(r_i),\\ Q_{ij} & o_{ij} \ne h_j(r_i),\end{cases}$$

with uniform priors except $P(h_1 = 0) = 1$, which removes the $h \leftrightarrow \bar h$ symmetry.

**Junction tree.** The clusters $C_j = \{h_j\} \cup \{r_i, o_{ij} : i \in R_j\}$, $j = 1, \dots, m$, joined in a path in order of $j$, form a valid junction tree: every factor lies in one cluster, and since a read's span is an interval, $r_l \in C_x \cap C_y$ with $x \le z \le y$ implies $r_l \in C_z$ (running intersection).

**Recursion.** With $R_{j \cap j+1} = R_j \cap R_{j+1}$, $R_{j \setminus j+1} = R_j \setminus R_{j+1}$, and $M_0 \equiv 0$, the max-sum messages are

$$M_j(r_{R_{j \cap j+1}}) = \max_{h_j}\, \max_{r_{R_{j \setminus j+1}}} \Bigl( \sum_{i \in R_j} \log P(o_{ij} \mid r_i, h_j) + M_{j-1}(r_{R_{j-1 \cap j}}) \Bigr),$$

and the maximum of the likelihood is the same expression at $j = m$ maximized over all of $R_m$; storing argmaxes recovers $(h^\ast, r^\ast)$. With coverage $\kappa = \max_j |R_j|$ the algorithm is exact and runs in $O(m\, \kappa\, 2^{\kappa + 1})$ time: linear in the number of sites, exponential only in coverage.

**Minimum error correction as a special case.** If $Q_{ij} \equiv q \in (0, \tfrac12)$, then

$$\log P(o = M \mid r, h) = \mathrm{const} - \log\frac{1 - q}{q} \cdot \#\{(i, j) : j \in \mathrm{Po}(i),\ M_{ij} \ne h_j(r_i)\},$$

so the maximum likelihood $(h, r)$ is exactly a minimum error correction (MEC) solution: the bipartition of reads and haplotype pair that requires the fewest allele flips.

## Proof depends on

- [Viterbi computes the MAP value](../../../ComputerScience/machine-learning/probabilistic-graphical-models/hidden-markov-models/sup-viterbi-eq.md)

## Expansion

The message $M_j$ is the best log-likelihood of the data at sites $1, \dots, j$ given the origins of the reads that continue to site $j + 1$; reads that end at $j$ are maximized out, and reads starting at $j + 1$ enter the next cluster. This is the Viterbi algorithm on a chain whose state at site $j$ is the origin vector of the spanning reads. Replacing max by sum gives marginal posteriors, which yield per-site confidence scores; this matters because two reads joined by an error-prone site can support two haplotypes (for example $00000$ and $00111$) with equal likelihood, so a phase can be uncertain even where reads overlap. Other variable orderings in the same graphical model give other exact dynamic programs for MEC.

## Sources

- V. Kuleshov, "Probabilistic single-individual haplotyping", Bioinformatics 30 (2014) i379–i385, Sections 4.1–4.4 (Definitions 1–3, Lemma 1, Equation (1), running time), <https://doi.org/10.1093/bioinformatics/btu484> (PMC4147930).
