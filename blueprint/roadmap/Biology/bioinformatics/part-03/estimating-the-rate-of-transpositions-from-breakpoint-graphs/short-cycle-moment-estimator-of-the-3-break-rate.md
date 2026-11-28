# Short-cycle moment estimator of the 3-break rate

**Setting.** Two genomes $P$ and $Q$ share $n$ synteny blocks, and their breakpoint graph $G(P,Q)$ is a disjoint union of alternating cycles. For circular genomes the 2-break distance is $d(P,Q)=n-c(P,Q)$, where $c$ counts cycles. Evolution from $P$ to $Q$ is modeled as a Markov chain of rearrangements on the $n$ fragile regions, the red edges. Each step is a 2-break (reversal, translocation, fusion, fission) with probability $1-p$ or a 3-break (which includes transpositions) with probability $p$. There are $k_2$ 2-breaks and $k_3$ 3-breaks, with breakpoints chosen uniformly. Under the fragile breakage model the total number $n$ of fragile regions is hidden: trivial 1-cycles are not observed. What is observed is the number $b=\sum_{\ell\ge2}\ell c_\ell$ of broken regions and the counts $c_\ell$ of $\ell$-cycles. The target is the transposition rate $p=k_3/(k_2+k_3)$.

**Approximate moment equations.** Let $\gamma=(2k_2+3k_3)/n$. To leading order in $1/n$, with $b=O(n)$:

1. a red edge escapes all rearrangements with probability $(1-\frac2n)^{k_2}(1-\frac3n)^{k_3}\approx e^{-\gamma}$, so $n-b\approx n\,e^{-\gamma}$;
2. 2-cycles arise mainly from single 2-breaks merging two untouched edges, so $c_2\approx k_2\,e^{-2\gamma}$;
3. 3-cycles arise from single 3-breaks on untouched edges, or from two successive 2-breaks sharing one edge, so $c_3\approx k_3e^{-3\gamma}+\frac{2k_2^2}{n}e^{-3\gamma}$.

The splitting of longer cycles into short ones has probability of order $b/n^2$ and is negligible.

**Estimator.** Eliminate $k_2$ and $n$ by taking a linear combination of these equations and substituting $n=b/(1-e^{-\gamma})$. This gives a single equation for $\gamma$:

$$\gamma e^{-3\gamma}\approx\frac{1-e^{-\gamma}}{b}\Big(2c_2e^{-\gamma}+3c_3-\frac{6c_2^2e^{\gamma}(1-e^{-\gamma})}{b}\Big).$$

Solving it numerically gives $\gamma^{\rm est}$. Then $n^{\rm est}=b/(1-e^{-\gamma^{\rm est}})$, $k_2^{\rm est}=c_2e^{2\gamma^{\rm est}}$, $k_3^{\rm est}=(n^{\rm est}\gamma^{\rm est}-2k_2^{\rm est})/3$, and

$$p^{\rm est}=\frac{k_3^{\rm est}}{k_2^{\rm est}+k_3^{\rm est}} .$$

The method uses only the observable $b$, $c_2$ and $c_3$, does not assume parsimony, and estimates the true number of rearrangements $k_2+k_3$, not just the 2-break distance. On simulated genomes it recovers $p$ accurately. Applied to mammalian genomes it estimates that about $26\%$ of rearrangements are transpositions, more than commonly assumed.

## Expansion

Each equation counts the ways a short cycle can be created from trivial cycles. A specific red edge is hit by exactly one 2-break with probability about $\frac{2k_2}{n}e^{-\gamma}$, and a second specified edge joins it in that 2-break with probability about $\frac1ne^{-\gamma}$. Summing over the $n(n-1)/2$ pairs gives $c_2\approx k_2e^{-2\gamma}$. For 3-cycles of the second type, one edge must be touched by two specific 2-breaks, probability about $2k_2^2e^{-\gamma}/n^2$, and the other two edges by exactly one each, probability about $(e^{-\gamma}/n)^2$. Over $n^3$ ordered triples this gives $\frac{2k_2^2}{n}e^{-3\gamma}$. The combination $2e^{-\gamma}\times$(the $c_2$ equation) $+\,3\times$(the $c_3$ equation) cancels $k_2$ and $k_3$ against $n\gamma=2k_2+3k_3$, which leaves the scalar equation.

These are the model of Section 3 and the estimates (Eqs. for $n-b$, $c_2$, $c_3$ and $\gamma$) of Section 4 of the source.

## Sources

- N. Alexeev, R. Aidagulov, M. A. Alekseyev, "A Computational Method for the Rate Estimation of Evolutionary Transpositions", arXiv:1501.07546 (2015). <https://doi.org/10.48550/arXiv.1501.07546>
