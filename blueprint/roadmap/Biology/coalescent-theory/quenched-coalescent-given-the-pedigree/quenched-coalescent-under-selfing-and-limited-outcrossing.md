# Quenched coalescent under selfing and limited outcrossing

Consider a diploid, monoecious population of constant size $N$ in discrete time steps with overlapping generations. At each step $K_N$ offspring replace $K_N$ uniformly chosen individuals; the exchangeable symmetric matrix $(V_{i,j})$ gives the number of offspring of each parent pair (with $V_{i,i}$ counting selfed offspring), and each offspring is selfed with probability $\alpha_N$. Let $c_N$ be the probability that two genes from distinct individuals coalesce in one step back, and $d_N=\frac{1-\alpha_N}{N}\mathbb{E}[K_N]$ the probability that two lineages in the same individual move to distinct individuals in one step back. For a sample of genes from $n$ individuals, let $\bar\chi^{N,n}(t)$ be the ancestral partition process (blocks = genes with a common ancestor, grouped by the individual carrying them) run on the time scale $\lfloor t/c_N\rfloor$ with a random time change that skips the instantaneous selfing collapses. Let $\mathcal G_N$ be the population pedigree and $\mathcal L^{N,n}=\mathbb P(\bar\chi^{N,n}\in\cdot\mid\mathcal G_N,\text{sampled individuals})$ the **quenched law**.

Assume (i) $c_N\to 0$; (ii) limited outcrossing: $\alpha_N\to 1$ and $d_N/c_N\to\lambda\in[0,\infty)$; (iii) the rescaled one-step transition matrices $c_N^{-1}(H_{N,n}-I)$ converge to a consistent family of rate matrices $Q_n$, so that by consistency there is a unique finite measure $\Xi$ on the ordered simplex with $Q_n$ the generator of the $n$-$\Xi$-coalescent.

1. (Annealed limit) The unconditional law of $\bar\chi^{N,n}$ converges in distribution in $\mathcal D(\mathbb R_+,\mathcal E_n)$ to the $n$-$\Xi$-coalescent.
2. (Quenched limit) Let $\Pi$ be an exchangeable fragmentation-coalescence process with Kingman coefficient $\Xi(\{0\})$, coagulation measure induced by $\Xi-\Xi(\{0\})\delta_0$, erosion rate $\lambda$ and no dislocation measure, and let $\mathcal L^n_\Pi$ be the conditional law, given $\Pi$, of $n$ coalescing random walks that move on the blocks of $\Pi$. Then $\mathcal L^{N,n}\to\mathcal L^n_\Pi$ weakly in distribution as random elements of $\mathcal M_1(\mathcal D(\mathbb R_+,\mathcal E_n))$.

Equivalently, the limit is described by a random graph in which each node splits into two at rate $\lambda$ (an outcrossing event seen backward in time) and groups of nodes merge according to $Q$; given the graph, sample lineages perform coalescing random walks on it. Because the graph is random, the conditional genealogy, and hence the conditional site frequency spectrum, does not average out over the pedigree when $\lambda<\infty$.

## Expansion

Under near-complete selfing an individual's two gene copies trace back through a single line of selfed ancestors, interrupted by rare outcrossing events at rate $\lambda$ on the coalescent time scale. Fixing the pedigree fixes these events and the reproduction events that cause mergers, which in the limit form an exchangeable fragmentation-coalescence trajectory. Sample lineages then choose among the two parents at each outcrossing independently, giving coalescing random walks on that trajectory. The proof shows convergence of the discrete ancestral graph to the limiting graph and continuity of the walk law in the graph, combined with a criterion for weak convergence in distribution of random measures via integral functionals. Averaging over the graph recovers the annealed $\Xi$-coalescent.

## Depends on

- [Merger rates of a coalescent with simultaneous multiple collisions](../coalescents/xi-coalescents-simultaneous-multiple-collisions.md)

## Sources

- Louis Wai-Tong Fan, Maximillian Newman, John Wakeley, "Quenched coalescent for diploid population models with selfing and overlapping generations", arXiv:2510.26115 (2025), Theorems 3.11 and 4.7, <https://doi.org/10.48550/arXiv.2510.26115>
