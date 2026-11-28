# Kingman limit of the autotetraploid coalescent with $N_e = 4N$

For the monoecious autotetraploid Wright–Fisher model with tetrasomic inheritance and no double reduction, sample $n$ lineages, with $n$ held fixed as $N \to \infty$. As $N \to \infty$ with time rescaled in units of $N$ generations, the ancestral process converges weakly to a continuous-time Markov chain in which movement of lineages between individuals is instantaneous and each pair of lineages coalesces at rate $1/4$. Equivalently, measuring time in units of

$$N_e = 4N$$

generations, the limit is Kingman's $n$-coalescent, in which each of the $\binom{n}{2}$ pairs coalesces at rate one. The coalescent effective population size of an autotetraploid species is therefore four times the census number of individuals, and existing coalescent simulators apply after this rescaling of the time axis.

**Scope.** The source derives this limit exactly only for $n = 2$ and $n = 4$, by Möhle's two-timescale theorem applied to the full chain of configurations. For general $n$ it extends the limit by a heuristic reduction to three aggregate states, supported by numerical computation for finite $N$, without a proof for $n \notin \{2, 4\}$.

## Depends on

- [Pairwise ancestral process of an autotetraploid Wright–Fisher population](pairwise-ancestral-process-of-an-autotetraploid-population.md)
- [Rate matrix of Kingman's partition-valued coalescent](../../partition-valued-kingman-coalescent/partition-rate.md)

## Proof depends on

- [Möhle's lemma on Markov chains with two time scales](../../../../Probability/markov-chains/finite-markov-chains/mohle-s-separation-of-timescales-lemma-for-finit.md)

## Expansion

Write the one-generation matrix as $P = F + S/N + o(1/N)$ with $F = \lim_{N\to\infty} P$ collecting the $O(1)$ (fast) movements of lineages between gametes and individuals and $S = \lim_{N\to\infty} N(P - F)$ collecting the $O(1/N)$ (slow) coalescence events. Möhle's two-timescale theorem states that if $E = \lim_{t\to\infty} F^t$ exists then $\lim_{N\to\infty} P^{\lfloor Nt \rfloor} = E e^{tG}$ with generator $G = E S E$. For $n = 2$ one gets

$$F = \begin{pmatrix} \tfrac13 & \tfrac23 & 0 \\ 0 & 1 & 0 \\ 0 & 0 & 1\end{pmatrix}, \qquad E = \begin{pmatrix} 0 & 1 & 0 \\ 0 & 1 & 0 \\ 0 & 0 & 1\end{pmatrix}, \qquad G = \begin{pmatrix} 0 & -\tfrac14 & \tfrac14 \\ 0 & -\tfrac14 & \tfrac14 \\ 0 & 0 & 0 \end{pmatrix},$$

so a pair of lineages first scatters into different individuals and then coalesces at rate $1/4$ per unit of $N$ generations. For $n = 4$ the same computation over the seven configurations of four lineages gives an instantaneous jump to the state in which all four lineages are in different individuals and a single-coalescence rate $6 \times (1/4) = 3/2 = \binom{4}{2}/4$, while simultaneous multiple coalescences vanish in the limit: four lineages inside one individual are overwhelmingly more likely to be descended from two pairs in two different individuals. For general $n$ the source argues heuristically that the states "$n$ lineages in $n-1$ individuals", "$n$ lineages in $n$ individuals" and "a coalescence has occurred" suffice, and applying Möhle's theorem to this reduced chain gives pairwise coalescence at rate $\binom{n}{2}/4$; the reduction is not justified there, so this step is not a proof. Numerically, the probabilities of a single (rather than multiple) coalescence and of residence in the fully scattered state approach one quickly: the approximation is accurate already for population sizes of order one hundred.

## Sources

- B. Arnold, K. Bomblies, J. Wakeley, "Extending coalescent theory to autotetraploids", *Genetics* 192 (2012), 195–204, <https://doi.org/10.1534/genetics.112.140582> (PMC3430536). Theory, "Extension to larger samples", "Accuracy for finite $N$" and "Extension to arbitrary sample size $n$".
- M. Möhle, "A convergence theorem for Markov chains arising in population genetics and the coalescent with selfing", *Adv. Appl. Probab.* 30 (1998), 493–512, <https://doi.org/10.1239/aap/1035228080>.
