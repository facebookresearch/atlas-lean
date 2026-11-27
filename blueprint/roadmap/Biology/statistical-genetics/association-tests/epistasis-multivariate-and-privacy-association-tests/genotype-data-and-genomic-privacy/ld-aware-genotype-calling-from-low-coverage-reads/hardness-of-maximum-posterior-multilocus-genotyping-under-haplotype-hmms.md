# Hardness of maximum-posterior multilocus genotyping under haplotype HMMs

**Model.** At SNP loci $1,\dots,n$ an individual carries a maternal and a paternal allele $H_i, H'_i \in \{0,1\}$, and its genotype is $g_i = H_i + H'_i \in \{0,1,2\}$. Each parental haplotype is emitted by a left-to-right hidden Markov model ($M$ for the maternal side, $M'$ for the paternal side) whose hidden states $F_i$ are founder haplotypes, so that a haplotype is a mosaic of $K$ founders produced by historical recombination, with transition and emission probabilities trained on a reference panel. Reads $r_i$ covering locus $i$ depend only on $g_i$, through a sequencing-error model in which a read at a heterozygous locus reports either allele with probability $1/2$ (the chromosome it was sampled from) and errs with the base-call error probability. The multilocus genotyping problem (MGP) asks for

$$g^* = \arg\max_{g\in\{0,1,2\}^n} P(g \mid r, M, M').$$

**Theorem.** The optimization version (maximum multilocus genotype probability) cannot be approximated within the polynomial factors that apply to the most probable string emitted by a hidden Markov model (unless P = NP, respectively ZPP = NP), even when $M' = M$. Consequently MGP is NP-hard. In contrast, the marginal posterior $P(g_i \mid r, M, M')$ of each single-locus genotype is computable in polynomial time by a forward–backward recursion on the product chain of founder pairs, which yields the posterior-decoding caller $\hat g_i = \arg\max_{g_i} P(g_i \mid r, M, M')$.

## Depends on

- [Hidden Markov model](../../../../../../ComputerScience/machine-learning/probabilistic-graphical-models/hidden-markov-models/hmm.md)

## Proof depends on

- [The likelihood from the forward and backward variables](../../../../../../ComputerScience/machine-learning/probabilistic-graphical-models/hidden-markov-models/likelihood-eq-sum-forward-mul-backward.md)

## Expansion

The reduction starts from the problem of the most probable 0/1 string of fixed length emitted by a left-to-right HMM $M_0$, which is inapproximable by an approximation-preserving reduction from clique. Build $M = M'$ by prefixing one extra locus with two founders, one emitting $0$ followed by a chain of all-$0$ founders and one emitting $1$ followed by the states of $M_0$, and supply error-free reads supporting both alleles at the first locus. Then only genotypes with $g_1 = 1$ and $g_i \in \{0,1\}$ for $i \ge 2$ have positive posterior, each arising exactly when one haplotype is all zeros and the other is $g$, so

$$P(g \mid r, M, M') = c\cdot P(g_2,\dots,g_n \mid M_0)$$

for a constant $c$, and maximizing the genotype posterior is maximizing the emitted-string probability. Marginals stay tractable because summing over hidden founder pairs is a standard forward–backward computation with $K^2$ states per locus, which is what makes posterior decoding the practical choice.

## Sources

- J. Duitama, J. Kennedy, S. Dinakar, Y. Hernández, Y. Wu, I. I. Măndoiu, "Linkage disequilibrium based genotype calling from low-coverage shotgun sequencing reads", BMC Bioinformatics 12(Suppl 1):S53 (2011), Eqs (1)–(7), the HF-HMM model, Theorem 1 and Corollary 2, <https://doi.org/10.1186/1471-2105-12-S1-S53>, PMCID PMC3044311.
