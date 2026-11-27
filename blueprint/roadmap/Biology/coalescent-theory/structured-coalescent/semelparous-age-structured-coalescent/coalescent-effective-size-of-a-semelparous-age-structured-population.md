# Coalescent effective size of a semelparous age-structured population

Consider a haploid population of constant total size $N$ divided into five age classes, with $N_i$ individuals of age $i$. Reproduction is semelparous: no individual survives reproduction and none lives past age five, individuals of ages three to five spawn, and a proportion $p_i$ of the newborns have a parent of age $i$, with $\sum_i p_i = 1$. Let $D_i$ be the number of individuals of age class $i$ that die each year and $c_i = D_i/N$ the corresponding fraction of the population, so $N_{i+1} = N_i - D_i$ and $N_5 = D_5$. Within an age class reproduction is Wright–Fisher: each of the $p_i N_1$ offspring produced by class $i$ picks its parent uniformly among the $D_i$ spawners of that class.

Sample two lineages and record the pair of age classes they occupy, together with an absorbing coalesced state; this is a Markov chain on $5^2 + 1 = 26$ states. Because the species is semelparous, **a pair of lineages can coalesce in one step if and only if both lineages are in age class one in the preceding step**. Movement of lineages between age classes happens with probability $O(1)$ per generation while coalescence happens with probability $O(1/N)$, so the chain has two timescales; assuming at least two of $p_3, p_4, p_5$ are positive (so the single-lineage age chain is irreducible and aperiodic, since any two of $3, 4, 5$ are coprime), as $N \to \infty$ it converges weakly to Kingman's coalescent once time is measured in units of a coalescent effective size

$$N_e = \kappa\, N,$$

where $\kappa$ is determined by the stationary distribution of the age-class movement and by the per-step coalescence probability from the doubly-young state. The coalescent effective size is a function of the relative contributions $p_i$ of the age classes and of the relative mortalities $c_i$, that is, of age-dependent fecundity and of the expected generation time; in the degenerate periodic case where only one age class reproduces ($p_3 = p_4 = 0$, $p_5 = 1$, so $N_1 = \cdots = N_5$ and $c_5 = 0.2$), the chain has period $5$ and splits into five reproductively isolated year-class lines; two lineages sampled in the same age class coalesce at effective size $N_e = N$ (in years), whereas lineages in different age classes never coalesce.

## Depends on

- [Rate matrix of Kingman's partition-valued coalescent](../../partition-valued-kingman-coalescent/partition-rate.md)
- [Finite-state Markov chain with a given transition matrix](../../../../Probability/markov-chains/finite-markov-chains/is-finite-markov-chain.md)

## Proof depends on

- [Möhle's lemma on Markov chains with two time scales](../../../../Probability/markov-chains/finite-markov-chains/mohle-s-separation-of-timescales-lemma-for-finit.md)
- [Uniqueness of the stationary distribution of a primitive chain](../../../../Probability/markov-chains/convergence-theorem-for-finite-markov-chains/stationary-unique.md)
- [Convergence of matrix powers to the stationary distribution](../../../../Probability/markov-chains/convergence-theorem-for-finite-markov-chains/tendsto-pow-apply.md)

## Expansion

Write the one-generation matrix as $P = A + B/N + o(1/N)$, with $A$ the fast age-class movements and $B$ the slow coalescence events; the single nonzero slow entry corresponds to the state in which both lineages sit in age class one. Möhle's theorem gives the limit $\lim_{N\to\infty} P^{\lfloor Nt\rfloor} = \Pi e^{tG}$ with $\Pi = \lim_{t\to\infty} A^t$ and generator $G = \Pi B \Pi$. The single-lineage chain over the five age classes — a lineage of age $i>1$ was of age $i-1$ one year earlier, and a lineage of age one descends from a parent of age $k$ with probability $p_k$ — is irreducible, aperiodic and positive recurrent, so it has a unique stationary distribution, and the two-lineage movement matrix is the Kronecker product of the single-lineage matrix with itself, which makes $\Pi$ explicit and much cheaper to compute than a direct limit of the $26 \times 26$ matrix. Since the last column of $\Pi$ vanishes except in the absorbing row, $G$ has a single coalescence rate, and rescaling time by it yields rate one per pair, that is, Kingman's coalescent. Because the coalescent effective size exists, every prediction of coalescent theory applies to this life history after the rescaling, which is the advantage of this notion of effective size over the variance and inbreeding effective sizes, each of which would require a separate calculation.

## Sources

- C. Cenik, J. Wakeley, "Pacific salmon and the coalescent effective population size", *PLoS ONE* 5 (2010), e13019, <https://doi.org/10.1371/journal.pone.0013019> (PMC2946355). Methods, "Model", "The Ancestral Process" and "Weak Convergence to Kingman's Coalescent".
- M. Möhle, "A convergence theorem for Markov chains arising in population genetics and the coalescent with selfing", *Adv. Appl. Probab.* 30 (1998), 493–512, <https://doi.org/10.1239/aap/1035228080>.
