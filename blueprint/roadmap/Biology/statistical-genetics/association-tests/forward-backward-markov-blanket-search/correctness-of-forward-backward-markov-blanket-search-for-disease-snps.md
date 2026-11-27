# Correctness of forward–backward Markov blanket search for disease SNPs

Let $V$ be a finite set of discrete variables (SNP genotypes and a disease status $T$) with joint distribution $J$ that is faithful to a directed acyclic graph $G$ on $V$: the conditional independences of $J$ are exactly those implied by d-separation in $G$. The Markov blanket $\mathrm{MB}(T)$ is the minimal set with $T \perp X \mid \mathrm{MB}(T)$ for all $X \notin \mathrm{MB}(T) \cup \{T\}$; under faithfulness it is unique and equals the parents, children and co-parents of $T$. Then:

1. (Adjacency) $X$ and $Y$ are adjacent in $G$ iff they are dependent given every subset of $V \setminus \{X, Y\}$.
2. (Parents only) If $\mathrm{MB}(T)$ consists only of parents of $T$, every $X \in \mathrm{MB}(T)$ is dependent on $T$ given every subset of $V \setminus \{T, X\}$.
3. (Shielding) If $X \notin \mathrm{MB}(T)$, then $T \perp X \mid S$ for every $S \supseteq \mathrm{MB}(T)$ with $X \notin S$.
4. (Correctness) Consider the search that, in a forward phase, repeatedly adds to a candidate set $\widehat{\mathrm{MB}}$ the variable most dependent on $T$ given $\widehat{\mathrm{MB}}$ until no remaining variable is dependent on $T$ given $\widehat{\mathrm{MB}}$, and in a backward phase removes every $X \in \widehat{\mathrm{MB}}$ that is independent of $T$ given some subset of $\widehat{\mathrm{MB}} \setminus \{X\}$. If every conditional-independence test returns the correct answer and disease status has no children in $G$ (so that $\mathrm{MB}(T)$ is the set of parents of $T$), the search returns exactly the parents of $T$.

## Depends on

- [d-separation](../../../../ComputerScience/machine-learning/probabilistic-graphical-models/causal-bayesian-networks/dseparated.md)
- [Markov Blanket](../../../../ComputerScience/machine-learning/probabilistic-graphical-models/bayesian-networks/markov-blanket.md)

## Proof depends on

- [The Markov blanket d-separates a node from all other nodes](../../../../ComputerScience/machine-learning/probabilistic-graphical-models/bayesian-networks/d-separated-markov-blanket.md)

## Expansion

Statement 1 is the standard characterization of adjacency in faithful DAG models; statement 2 follows because every parent is adjacent to $T$. Statement 3 is the weak-union property applied to $T \perp X \mid \mathrm{MB}(T)$. For statement 4, the forward phase stops only when the candidate set shields $T$ from everything outside it, so it contains $\mathrm{MB}(T)$; by statement 2 no true parent can be removed in the backward phase, and by statement 3 every false positive becomes independent of $T$ given a subset containing $\mathrm{MB}(T)$ and is removed. In practice the independence tests are $G^2$ likelihood-ratio tests on genotype contingency tables, and the search detects SNPs that act on disease only jointly (epistasis).

## Sources

- B. Han, X.-W. Chen and Z. Talebizadeh, "FEPI-MB: identifying SNPs-disease association using a Markov Blanket-based approach", BMC Bioinformatics 12 (Suppl. 12) (2011) S3, <https://doi.org/10.1186/1471-2105-12-S12-S3>, PMCID PMC3247084. Definition 1 and Theorems 1–5.
