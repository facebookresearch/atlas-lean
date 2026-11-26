# Look-ahead gamete distribution under recurrent paired mating

Consider $L$ ordered biallelic loci with adjacent recombination frequencies $r = (r_1, \dots, r_{L-1}) \in [0, 1/2]^{L-1}$ and a diploid population in generation $t$ with genotype array $G \in \{0,1\}^{L \times 2 \times S}$ ($G_{l,m,i}$ is the allele at locus $l$ on haplotype $m \in \{1,2\}$ of individual $i$), $S$ even. Individuals $2j-1$ and $2j$ are mated, $j = 1, \dots, S/2$, and the **look-ahead simulation** assumes (i) each selected pair produces one progeny in generation $t+1$, and (ii) from generation $t+1$ to $T-1$ crosses are made within the same generation, each producing one progeny, under Haldane-type independent recombination between adjacent loci.

**Theorem.** Let $g \in \{0,1\}^L$ be a random gamete produced in meiosis of generation $T-1$, and write $g_l = G_{l,m,i}$ to mean that the allele at locus $l$ traces back to haplotype $m$ of founder $i$. Then

$$P(g_1 = G_{1,m,i}) = \frac{1}{2S}, \qquad i \in \{1,\dots,S\},\ m \in \{1,2\},$$

and the founder origin is a Markov chain along the loci with transition probabilities

$$P\big(g_{l+1} = G_{l+1,m_1,i_1} \,\big|\, g_l = G_{l,m_0,i_0}\big) = \begin{cases} (1-r_l)^2 (1-R_l), & i_0 = i_1,\ m_0 = m_1,\\ r_l(1-r_l)(1-R_l), & i_0 = i_1,\ m_0 \ne m_1,\\ \tfrac12\, r_l (1 - R_l), & i_0 \ne i_1,\ \lceil i_0/2 \rceil = \lceil i_1/2 \rceil,\\ \dfrac{R_l}{2(S-2)}, & \lceil i_0/2 \rceil \ne \lceil i_1/2 \rceil, \end{cases}$$

where $R_l$, the probability that the founder pair changes between loci $l$ and $l+1$ over the later generations, is

$$R_l = \frac{S-2}{S}\,\big[1 - (1 - r_l)^{T-t}\big].$$

The **look-ahead objective** $f_{\mathrm{LAS}}(x, y, r, T-t)$ (selection $x$, mating $y$) is the expected maximum GEBV in generation $T$; it is approximated by sampling gametes from this chain, pairing them into individuals, scoring each by additive marker effects, and taking the largest.

## Depends on

- [Haldane's map function](../../population-genetics/linkage-disequilibrium-and-haldane-s-map-functio/haldane.md)

## Proof depends on

Its proof consists of the steps listed under Expansion.

## Expansion

The first meiosis inside a mated pair contributes the factors $(1-r)^2$, $r(1-r)$ and $r/2$: staying on the same parental haplotype, switching haplotype within the same parent, or switching to the mate. Thereafter the chromosome is reshuffled among the $S$ lineages; a junction between loci $l$ and $l+1$ survives $T-t$ meioses unbroken with probability $(1-r_l)^{T-t}$, and a break lands on one of the $S-2$ founders outside the pair with probability $(S-2)/S$, giving $R_l$; both $r_l$ and $R_l$ belong to the interval between loci $l$ and $l+1$ (the source's Eq. 12 writes $r_{l+1}, R_{l+1}$, which is undefined at $l = L-1$). The rows sum to one: $(1-R)\big[(1-r)^2 + r(1-r) + r\big] + R = 1$. Because $f_{\mathrm{LAS}}$ rewards the best terminal individual rather than the mean, it keeps diverse parents in the program and adapts to the deadline $T$.

## Sources

- S. Moeinizade, G. Hu, L. Wang and P. S. Schnable, "Optimizing selection and mating in genomic selection with a look-ahead approach: an operations research framework", G3: Genes|Genomes|Genetics 9 (2019), Methods ("Look-ahead selection"), Eqs. (7)–(13) and Theorem 1, <https://doi.org/10.1534/g3.118.200842>, PMCID: PMC6643893.
