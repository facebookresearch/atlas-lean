# Gap census for a target genome in metagenomic sequencing

**Stevens' theorem.** Place $n \ge 1$ arcs, each of length $a \in (0, 1)$ (as a fraction of the circumference), on a circle of circumference $1$, with independent uniformly distributed starting points. Let $G$ be the number of uncovered gaps and $K = \min(n, \lfloor 1/a \rfloor)$, the largest number of arcs that fit without overlap. Then for $g = 0, 1, \dots, K$

$$P(G = g) = \binom{n}{g} \sum_{k = g}^{K} (-1)^{k-g} \binom{n-g}{k-g} (1 - k a)^{n-1},$$

and in particular the circle is completely covered with probability

$$P(G = 0) = \sum_{k=0}^{K} (-1)^k \binom{n}{k} (1 - k a)^{n-1}.$$

**Metagenomic gap census.** A sample yields $N$ reads, each independently derived from a target species with probability $p$ (its relative abundance in the read pool); a target read covers a fraction $a$ of the target's (circularised, composite) genome. Let $G$ be the number of gaps in the target and $K = \min(N, \lfloor 1/a \rfloor)$. For $g \ge 1$,

$$P(G = g) = \sum_{k=g}^{K} (-1)^{k-g} \binom{k}{g} \binom{N}{k}\, p^{k}\, (1 - k a)^{k-1} (1 - p k a)^{N-k},$$

and the probability that the target receives at least one read and is completely covered is $1 - \sum_{g \ge 1} P(G = g)$. For $p = 1$ this reduces to Stevens' theorem with $n = N$.

## Expansion

Conditioning on the number $n \sim \mathrm{Bin}(N, p)$ of target reads, $P(G = g) = \sum_n \binom{N}{n}p^n(1-p)^{N-n}\, P_{\text{Stevens}}(G = g \mid n)$. Using $\binom{n}{g}\binom{n-g}{k-g} = \binom{n}{k}\binom{k}{g}$ and $\binom{N}{n}\binom{n}{k} = \binom{N}{k}\binom{N-k}{n-k}$ and exchanging the sums, the inner sum over $j = n - k$ is $\sum_j \binom{N-k}{j} \big(p(1-ka)\big)^{j}(1-p)^{N-k-j} = (1 - pka)^{N-k}$ by the binomial theorem, which leaves the closed form. Stevens' formula itself is inclusion–exclusion over the events that the $k$ chosen arcs are each followed by a gap: the probability that $k$ specified arcs all have uncovered space after them is $(1-ka)^{n-1}$. Because complete coverage requires all gaps to close, it is reached much later than high fractional coverage; for near-complete coverage the mean contig length is approximately the genome length divided by the number of gaps, so the gap census also yields tail probabilities for average contig size. Departures of observed coverage from the formula reflect sequence-dependent bias, which can be approximated by lowering the effective read length.

## Sources

- M. C. Wendl, K. Kota, G. M. Weinstock, M. Mitreva, "Coverage theories for metagenomic DNA sequencing based on a generalization of Stevens' theorem", Journal of Mathematical Biology 67 (2013) 1141–1161, Section 2 (Theorem 1, gap census; Corollary 1, complete coverage; Corollary 2, average contig size) and Methods (proof of Theorem 1 by binomial conditioning of Stevens' theorem), <https://doi.org/10.1007/s00285-012-0586-x> (PMC3795925).
- W. L. Stevens, "Solution to a geometrical problem in probability", Annals of Eugenics 9 (1939) 315–320, <https://doi.org/10.1111/j.1469-1809.1939.tb02216.x>.
