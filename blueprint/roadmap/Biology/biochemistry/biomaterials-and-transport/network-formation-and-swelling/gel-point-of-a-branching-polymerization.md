# Gel point of a branching polymerization

In Flory's tree model of branching step-growth polymerization with branch units of functionality $f \ge 3$, an infinite molecule (component) occurs with positive probability if and only if the branching coefficient exceeds $\alpha_c = 1/(f-1)$.

Let every branch unit carry $f \ge 3$ functional groups, joined to other branch units through chains of bifunctional units. The branching coefficient $\alpha \in [0,1]$ is the probability that a given arm of a branch unit leads, through a chain of bifunctional units, to another branch unit. Model the molecule containing a randomly chosen branch unit as a tree in which the arms are independent Bernoulli($\alpha$) trials; Flory motivates this by assuming (i) equal reactivity of all functional groups of one type, independent of the size of the molecule carrying them, and (ii) no intramolecular (ring-forming) bonds. Then each branch unit reached through one arm offers $f - 1$ further arms, the number of further branch units it reaches is Binomial($f-1, \alpha$) with mean $\alpha(f-1)$, and with

$$\alpha_c = \frac{1}{f-1}$$

the molecule is infinite with positive probability exactly when $\alpha > \alpha_c$. At $\alpha = \alpha_c$ the molecule is finite almost surely. For a trifunctional branching agent ($f = 3$) the threshold is $\alpha_c = 1/2$, the value Wen et al. quote before modifying $\alpha$ for chain terminators in their Eq. (20).

## Context

Graduate polymer chemistry. The threshold is a statement about the idealized tree model, not about any real formulation; relating $\alpha$ to measured conversions needs extents of reaction, stoichiometry and the fraction of groups on branch units, which Wen et al. handle separately (their Eq. (20)). In Artzi and co-workers' dendrimer-amine/dextran-aldehyde adhesives, amine density determines whether a mixture gels, stays liquid or polymerizes rapidly (Oliva et al., 2012); that observation motivates the page but is not a test of the formula. Wen et al. also report that the Flory–Stockmayer description loses accuracy near and above the gel point, where rings and loops matter.

## Depends on

None.

## Proof depends on

- [Galton–Watson extinction criterion](../../../../Probability/branching-processes/galton-watson-process/extinction-prob-eq-one-iff.md)

## Expansion

Proof route: the offspring law is Binomial($f-1, \alpha$), not concentrated at 1 for $f \ge 3$ and $\alpha < 1$, so the extinction criterion gives finite molecules almost surely iff the mean $\alpha(f-1) \le 1$. The case $\alpha = 1$ needs a one-line separate argument (deterministic offspring $f-1 \ge 2$). Still needed: a page defining $\alpha$ in terms of extents of reaction and the fraction of groups on branch units (Wen Eq. (20)), and the stoichiometric $A_f + B_g$ criterion relevant to star-PEG/dextran networks; neither is supplied here.

## Sources

- C. Wen, R. Odle and S. Cheng, "Molecular Weight Distribution of Branched Polymers: Comparison between Monte Carlo Simulation and Flory-Stockmayer Theory", Polymers 15(7), 1791 (2023), <https://doi.org/10.3390/polym15071791>; open-access copy read at <https://pmc.ncbi.nlm.nih.gov/articles/PMC10097263/> and <https://www.mdpi.com/2073-4360/15/7/1791>: Introduction (Flory's two assumptions and their limitation to the pre-gel regime) and the paragraph introducing Eq. (20), where $\alpha_c = 1/(g_2 - 1) = 1/2$ is quoted for $g_2 = 3$
- N. Oliva, S. Shitreet, E. Abraham, B. Stanley, E. R. Edelman and N. Artzi, "Natural Tissue Microenvironmental Conditions Modulate Adhesive Material Performance", Langmuir 28 (2012), <https://doi.org/10.1021/la303155p>; author manuscript read at <https://pmc.ncbi.nlm.nih.gov/articles/PMC4627478/>: the paragraph stating that, once dendrimer generation and oxidation level are fixed, amine density determines whether the material gels, remains a liquid or polymerizes rapidly
- P. J. Flory, "Molecular Size Distribution in Three Dimensional Polymers. I. Gelation", Journal of the American Chemical Society 63, 3083–3090 (1941), <https://doi.org/10.1021/ja01856a061>: original derivation, cited through Wen et al. and not read
