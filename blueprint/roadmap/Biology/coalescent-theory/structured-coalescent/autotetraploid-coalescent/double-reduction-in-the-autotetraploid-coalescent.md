# Double reduction in the autotetraploid coalescent

Let the autotetraploid model carry double reduction: at a locus distal to the centromere, a quadrivalent with a crossover between locus and centromere can send two sister chromatids to the same pole, so that a gamete carries two lineages that are automatically identical by descent. Let $\alpha$ be the probability of double reduction at the locus, which satisfies $0 \le \alpha \le 1/6$ and does not depend on $N$. For two lineages the one-generation matrix becomes

$$P = \begin{pmatrix} \tfrac{1-\alpha}{3} + \tfrac{1}{2N} & \tfrac{2}{3} - \tfrac{2}{3N} & \tfrac{\alpha}{3} + \tfrac{1}{6N} \\[2pt] \tfrac{3}{4N} & 1 - \tfrac{1}{N} & \tfrac{1}{4N} \\[2pt] 0 & 0 & 1\end{pmatrix},$$

so double reduction raises the coalescence probability out of the within-individual state by $\alpha/3$, an $O(1)$ amount, and leaves the between-individual row unchanged. In the limit $N \to \infty$ with time in units of $N$ generations,

$$E = \begin{pmatrix} 0 & \tfrac{2}{2+\alpha} & \tfrac{\alpha}{2+\alpha} \\ 0 & 1 & 0 \\ 0 & 0 & 1 \end{pmatrix}:$$

a pair sampled within one individual coalesces *instantaneously* with probability $\alpha/(\alpha+2)$, and otherwise scatters into different individuals, after which it coalesces at rate $\tfrac14 + \tfrac34\cdot\tfrac{\alpha}{\alpha+2}$. For $0 < \alpha \le 1/6$ this rate is strictly greater than $1/4$, so the limit is not Kingman's coalescent and the long-term coalescent effective size is smaller than $4N$. At the endpoint $\alpha = 0$ the instantaneous probability is $0$ and the rate is exactly $1/4$: the limit is Kingman's coalescent with effective size $4N$.

For a sample of $n$ lineages distributed as $k$ individuals holding two lineages, $l$ individuals holding three and $m$ individuals holding four, the number of instantaneous coalescences contributed by the doubly occupied individuals is $X \sim \mathrm{Binomial}(k, \alpha/(\alpha+2))$ by the triply occupied individuals $Y \sim \mathrm{Binomial}(l, 3\alpha/(\alpha+2))$, and, among the quadruply occupied individuals, the numbers $Z_1$, $Z_2$, $Z_3$ with one, two and no instantaneous coalescences satisfy

$$(Z_1, Z_2, Z_3) \sim \mathrm{Multinomial}\Bigl(m;\ \tfrac{12\alpha(1-\alpha)}{(\alpha+2)^2},\ \tfrac{9\alpha^2}{(\alpha+2)^2},\ \tfrac{4(1-\alpha)^2}{(\alpha+2)^2}\Bigr),$$

After this instantaneous adjustment the $n - X - Y - Z_1 - 2Z_2$ surviving lineages lie in distinct individuals and coalesce at rate $O(1/N)$.

## Depends on

- [Pairwise ancestral process of an autotetraploid Wright–Fisher population](pairwise-ancestral-process-of-an-autotetraploid-population.md)
- [Rate matrix of Kingman's partition-valued coalescent](../../partition-valued-kingman-coalescent/partition-rate.md)

## Proof depends on

- [Möhle's lemma on Markov chains with two time scales](../../../../Probability/markov-chains/finite-markov-chains/mohle-s-separation-of-timescales-lemma-for-finit.md)

## Expansion

The bound $\alpha \le 1/6$ comes from the meiotic mechanism: a quadrivalent with one crossover between locus and centromere sends the recombined chromosomes to the same pole at meiosis I with probability $1/3$, and the two sister chromatids go to the same pole at meiosis II with probability $1/2$. Smaller values arise when the locus is close to the centromere or when bivalents form. In the decomposition $P = F + S/N + o(1/N)$ the matrix $F$ now contains a coalescence entry $\alpha/3$, so coalescence occurs on both timescales; $E = \lim_t F^t$ gives the stated instantaneous probabilities. The structure mirrors the coalescent with partial selfing of Nordborg and Donnelly, in which lineages within one individual may coalesce immediately: maximal double reduction $\alpha = 1/6$ produces the same limiting ancestral process as a selfing rate $s = 1/4$, and the map between $\alpha$ and the equivalent $s$ is close to linear. The practical consequence is an excess of identity within individuals and a reduced effective size relative to $4N$.

## Sources

- B. Arnold, K. Bomblies, J. Wakeley, "Extending coalescent theory to autotetraploids", *Genetics* 192 (2012), 195–204, <https://doi.org/10.1534/genetics.112.140582> (PMC3430536). Theory, "An ancestral process with double reduction" and "The coalescent with double reduction for arbitrary $n$".
- M. Nordborg, P. Donnelly, "The coalescent process with selfing", *Genetics* 146 (1997), 1185–1195, <https://doi.org/10.1093/genetics/146.3.1185>.
