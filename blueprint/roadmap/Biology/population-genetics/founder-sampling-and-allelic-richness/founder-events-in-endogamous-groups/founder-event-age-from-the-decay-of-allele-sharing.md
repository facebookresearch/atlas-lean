# Founder event age from the decay of allele sharing

For two individuals from a group founded by few individuals $g$ generations ago, consider the number of alleles they share at each SNP (two genotypes identical by descent at a site differ by at most one allele). After subtracting the same quantity computed for pairs from different groups, assume the autocorrelation of allele sharing at genetic distance $x$ (in centimorgans) decays as $e^{-x/d}$. Since the haplotypes of the two individuals are separated by $2g$ meioses since the founders, $d \approx 100/(2g)$ cM, and the founder event is dated to

$$g \approx \frac{100}{2d}$$

generations ago.

## Expansion

A segment inherited identical by descent from a common ancestor $g$ generations back is broken by crossovers occurring as a Poisson process of rate $2g$ per Morgan along the two lines of descent, so the probability that identity at one site extends to a site $x$ Morgans away is $e^{-2gx}$. Converting to centimorgans divides the rate by 100. The source checks the procedure by simulation; for the Vysya the fitted decay constant is $0.461$ cM, giving $100/(2 \times 0.461) \approx 108$ generations.

## Sources

- D. Reich, K. Thangaraj, N. Patterson, A. L. Price and L. Singh, "Reconstructing Indian population history", *Nature* 461 (2009), 489–494, figure legend "Linkage disequilibrium based evidence for founder events in India" and main text on founder events, <https://doi.org/10.1038/nature08365> (PMC2842210).
