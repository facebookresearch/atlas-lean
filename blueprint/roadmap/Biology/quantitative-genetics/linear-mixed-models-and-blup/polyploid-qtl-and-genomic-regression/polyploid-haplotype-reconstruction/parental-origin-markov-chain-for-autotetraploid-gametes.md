# Parental-origin Markov chain for autotetraploid gametes

Let a tetraploid parent carry homologs labeled $1, 2, 3, 4$, and consider a diploid gamete it transmits, observed at markers $t = 1, \dots, M$ in map order, with genetic distance $d_t$ (Morgans) between markers $t$ and $t+1$. The hidden state at marker $t$ is the ordered pair of parental origins of the two gamete homologs. Conditional on the valent formation $v$ of the meiosis, the origin process is a Markov chain with no crossover interference.

1. **Bivalent pairing**, $v \in \{[1{:}2][3{:}4],\ [1{:}3][2{:}4],\ [1{:}4][2{:}3]\}$. For $v = [1{:}2][3{:}4]$ the initial law is uniform on $\{(1,3), (1,4), (2,3), (2,4)\}$ and the transition matrix is $P_{\mathrm{bi}} \otimes P_{\mathrm{bi}}$, where

$$P_{\mathrm{bi}} = \begin{pmatrix} 1 - r_{\mathrm{bi}} & r_{\mathrm{bi}} \\ r_{\mathrm{bi}} & 1 - r_{\mathrm{bi}} \end{pmatrix}, \qquad r_{\mathrm{bi}} = \tfrac12\bigl(1 - e^{-2d_t}\bigr),$$

acting on origins $\{1, 2\}$ for the first gamete homolog and $\{3, 4\}$ for the second; the other bivalent configurations are analogous.

2. **Quadrivalent pairing**, $v = [1{:}2{:}3{:}4]$. The initial law is uniform on the $16$ ordered pairs in $\{1,2,3,4\}^2$ and the transition matrix is $P_{\mathrm{quad}} \otimes P_{\mathrm{quad}}$, with

$$P_{\mathrm{quad}} = (1 - r_{\mathrm{quad}})\, I_4 + \frac{r_{\mathrm{quad}}}{3}\,(J_4 - I_4), \qquad r_{\mathrm{quad}} = \tfrac34\bigl(1 - e^{-4d_t/3}\bigr),$$

where $J_4$ is the all-ones matrix: along each gamete homolog the origin switches to each of the other three origins with probability $r_{\mathrm{quad}}/3$.

A zygote is the Kronecker product of two independent gamete chains (one per parent, or two from the same parent under selfing), and the valent formations carry the prior $1/4$ on each of the three bivalents and the quadrivalent. Both $r_{\mathrm{bi}}$ and $r_{\mathrm{quad}}$ are increasing in $d_t$, vanish at $d_t = 0$ and tend to the free-recombination values $1/2$ and $3/4$, the probabilities that two independent uniform draws from $2$ or $4$ origins differ.

## Depends on

- [Haldane's map function](../../../../population-genetics/linkage-disequilibrium-and-haldane-s-map-functio/haldane.md)

## Expansion

$r_{\mathrm{bi}}$ is Haldane's map function: the probability of an odd number of Poisson crossovers with mean $d$. $r_{\mathrm{quad}}$ is the corresponding quantity for a continuous-time chain that jumps at rate $1$ per Morgan to a uniformly chosen other origin among four: its transition matrix is $e^{d(J_4 - 4I_4)/3}$, whose off-diagonal mass is $\tfrac34(1 - e^{-4d/3})$ because $J_4$ has eigenvalues $4$ and $0$. The quadrivalent chain is a statistical rather than mechanistic model of double reduction.

## Sources

- C. Zheng, R. R. Amadeu, P. R. Muñoz and J. B. Endelman, *Haplotype reconstruction in connected tetraploid F1 populations*, Genetics 219 (2021), iyab106, <https://doi.org/10.1093/genetics/iyab106>, PMCID PMC8633103 (PolyOrigin model: parental origin process; Table 1).
