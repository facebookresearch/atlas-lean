# Gel point of a branching polymerization

In Flory's tree model of branching step-growth polymerization with branch units of functionality $f \ge 3$, an infinite molecule (component) occurs with positive probability if and only if the branching coefficient exceeds $\alpha_c = 1/(f-1)$.

Let every branch unit carry $f \ge 3$ functional groups, joined to other branch units through chains of bifunctional units. The branching coefficient $\alpha \in [0,1]$ is the probability that a given arm of a branch unit leads, through a chain of bifunctional units, to another branch unit. Model the molecule containing a randomly chosen branch unit as a tree in which the arms are independent Bernoulli($\alpha$) trials; this idealization rests on (i) equal reactivity of all functional groups of one type, independent of the size of the molecule carrying them, and (ii) no intramolecular (ring-forming) bonds. Then each branch unit reached through one arm offers $f - 1$ further arms, the number of further branch units it reaches is Binomial($f-1, \alpha$) with mean $\alpha(f-1)$, and with

$$\alpha_c = \frac{1}{f-1}$$

the molecule is infinite with positive probability exactly when $\alpha > \alpha_c$, and finite almost surely when $\alpha \le \alpha_c$. In probabilistic terms this is percolation on the $f$-regular tree, whose critical probability is $1/(f-1)$ with no infinite cluster at criticality (Yadin, Theorem 5.8); Gilormini derives the same criterion in branching-process form for units of functionality $f$, with $\alpha$ the fraction of reacted groups (Flory's gelation condition); Wen et al. quote $\alpha_c = 1/(g_2 - 1) = 1/2$ for a trifunctional branching agent before modifying $\alpha$ for chain terminators in their Eq. (20).

## Context

Graduate polymer chemistry. The threshold is a statement about the idealized tree model, not about any real formulation; relating $\alpha$ to measured conversions needs extents of reaction, stoichiometry and the fraction of groups on branch units, which Wen et al. handle separately (their Eq. (20)). In dendrimer-amine/dextran-aldehyde adhesives, amine density determines whether a mixture gels, stays liquid or polymerizes rapidly (Oliva et al., 2012); that observation motivates the page but is not a test of the formula. Gilormini notes that cyclization is neglected in this theory although intramolecular reactions can matter. Wen et al. also report that the Flory–Stockmayer description loses accuracy near and above the gel point, where rings and loops matter.

## Depends on

None.

## Proof depends on

- [Galton–Watson extinction criterion](../../../../Probability/branching-processes/galton-watson-process/extinction-prob-eq-one-iff.md)

## Expansion

Proof route (as in Yadin, Proposition 5.7 and Theorem 5.8): the chosen unit has $f$ arms; each open arm leads to a subtree in which every unit offers $f - 1$ further arms, so the generation sizes in each subtree form a Galton–Watson process with Binomial($f-1, \alpha$) offspring. The molecule is infinite exactly when some arm of the chosen unit is open and the subtree beyond that arm, considered without it, contains an infinite cluster from its first unit. Since $f - 1 \ge 2$, the offspring law is never concentrated at 1 (including $\alpha = 1$), so by the extinction criterion each subtree's cluster is infinite with positive probability iff $\alpha(f-1) > 1$. If $\alpha(f-1) > 1$, then $\alpha > 0$, so an open arm with a surviving subtree has positive probability; if $\alpha(f-1) \le 1$, every subtree's cluster is finite almost surely, and so is the molecule. Still needed: a page defining $\alpha$ in terms of extents of reaction and the fraction of groups on branch units (Wen Eq. (20)), and the stoichiometric $A_f + B_g$ criterion relevant to star-PEG/dextran networks; neither is supplied here.

## Sources

- C. Wen, R. Odle and S. Cheng, "Molecular Weight Distribution of Branched Polymers: Comparison between Monte Carlo Simulation and Flory-Stockmayer Theory", Polymers 15(7), 1791 (2023), <https://doi.org/10.3390/polym15071791>; open-access copy read at <https://pmc.ncbi.nlm.nih.gov/articles/PMC10097263/> and <https://www.mdpi.com/2073-4360/15/7/1791>: Introduction (Flory's two assumptions and their limitation to the pre-gel regime) and the paragraph introducing Eq. (20), where $\alpha_c = 1/(g_2 - 1) = 1/2$ is quoted for $g_2 = 3$
- N. Oliva, S. Shitreet, E. Abraham, B. Stanley, E. R. Edelman and N. Artzi, "Natural Tissue Microenvironmental Conditions Modulate Adhesive Material Performance", Langmuir 28 (2012), <https://doi.org/10.1021/la303155p>; author manuscript read at <https://pmc.ncbi.nlm.nih.gov/articles/PMC4627478/>: the paragraph stating that, once dendrimer generation and oxidation level are fixed, amine density determines whether the material gels, remains a liquid or polymerizes rapidly
- A. Yadin, "Percolation", lecture notes, Ben-Gurion University of the Negev, author's copy read at <https://www.math.bgu.ac.il/~yadina/teaching/percolation/percolation.pdf>: Section 5.4 "Percolation on Regular Trees", Proposition 5.7 (the root cluster of a rooted regular tree is a Galton–Watson process with Binomial($d-1, p$) offspring) and Theorem 5.8 ($p_c(T_d) = 1/(d-1)$ and $\Theta_{T_d}(p_c) = 0$ for $d \ge 3$, proved by splitting at the root's $d$ neighbours)
- P. Gilormini, "An introduction to the statistical theory of polymer network formation", in R. E. Morris (ed.), The Sol-Gel Process: Uniformity, Polymers and Applications, Chap. 29, pp. 835–863, Nova Science Publishers (2011); author-deposited copy read at <https://sam.ensam.eu/bitstream/handle/10985/6886/StatisticalTheory.pdf>: section "Mathematical background" (branching process: the family tree is inevitably finite if $p \le 1/(f - 1)$, Eq. (10) and the text after it) and section "A first application" (equal reactivity; a unit with an infinite number of descendants belongs to the gel; Flory condition $x_g = 1/(f - 1)$, Eq. (11)); concluding remarks on neglected cyclization
- P. J. Flory, "Molecular Size Distribution in Three Dimensional Polymers. I. Gelation", Journal of the American Chemical Society 63, 3083–3090 (1941), <https://doi.org/10.1021/ja01856a061>: original derivation, cited through Wen et al. and Gilormini and not read
