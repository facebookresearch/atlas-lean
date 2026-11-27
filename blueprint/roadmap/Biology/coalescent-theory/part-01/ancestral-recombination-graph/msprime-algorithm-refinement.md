# msprime's segment representation of Hudson's algorithm

msprime implements Hudson's algorithm for the coalescent with recombination on explicit segments of ancestral material (Kelleher, Etheridge and McVean 2016, section "Efficient coalescent simulation"). A segment $(\ell, r, u)$ maps the half-open genomic interval $[\ell, r)$ to a tree node $u$; each ancestor is a set of non-overlapping segments, and the $n$ samples start as single segments $(0, m, u)$ over $m \ge 2$ loci. With $P$ the set of ancestors, recombination events occur at rate $\rho L/(m - 1)$, where $L$ is the number of available links (for each ancestor, the distance between the left end of its leftmost segment and the right end of its rightmost segment, minus one), and split one ancestor's segments at the chosen link; common ancestor events occur at rate $|P|(|P| - 1)$ in the paper's time units and merge two ancestors. Overlapping segments are first subdivided into their intersections and overhangs; each intersection becomes one coalescence record for a new node, while non-overlapping segments are carried over unchanged. The coalescence records are the output, from which the marginal trees are recovered. Baumdicker et al. (2022, section "Recombination") note that common ancestor events between ancestors with no overlapping segments create ancestors carrying trapped material, in which further recombinations occur, and cite $\rho(\rho + 1)(\sum_{i=1}^{n-1} 1/i)^2$ (their equation (1), taken from Hein et al. 2004) as an upper bound on the number of recombination events in trapped material, matching the observed quadratic growth of running time in $\rho$; Kelleher, Etheridge and McVean (2016, Fig. 2) observe this growth numerically, in contrast to the known upper bound $e^\rho$ on the number of recombination events in Hudson's algorithm.

## Expansion

1. The segment representation of an ancestor and the link count $L$, with the recombination rate $\rho L/(m - 1)$ and the uniform choice of a link.
2. The common ancestor update: subdivision into intersections and overhangs, one coalescence record per intersection, and removal of intervals whose most recent common ancestor has been reached.
3. Validity of the output: the coalescence records form a tree sequence whose marginal tree at each locus is the genealogy built at that locus.
4. The bound of equation (1) of Baumdicker et al. on recombinations in trapped material, and the resulting quadratic bound on expected running time in $\rho$.

## Sources

- J. Kelleher, A. M. Etheridge and G. McVean, Efficient coalescent simulation and genealogical analysis for large sample sizes, PLoS Comput. Biol. 12 (2016), e1004842, section "Efficient coalescent simulation", Introduction and Fig. 2. <https://doi.org/10.1371/journal.pcbi.1004842>
- F. Baumdicker et al., Efficient ancestry and mutation simulation with msprime 1.0, Genetics 220 (2022), iyab229, section "Recombination" and equation (1). <https://doi.org/10.1093/genetics/iyab229>
