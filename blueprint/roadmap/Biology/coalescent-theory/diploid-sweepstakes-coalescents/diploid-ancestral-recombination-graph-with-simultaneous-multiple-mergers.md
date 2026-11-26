# Diploid ancestral recombination graph with simultaneous multiple mergers

**Population model.** A population of $N$ diploid, biparental individuals carries chromosomes with $L$ loci and evolves in discrete Moran-type steps. With probability $1 - \varepsilon_N$ a *small* reproduction event occurs: one individual dies and is replaced by the offspring of two randomly chosen parents. With probability $\varepsilon_N$ a *large* (sweepstakes) event occurs: a fraction $\psi \in (0,1)$ of the population, $\lfloor\psi N\rfloor$ individuals, dies and is replaced by offspring of a single pair of parents. Every offspring receives exactly one chromosome from each parent, recombined between loci $\ell$ and $\ell + 1$ with probability $r_N^{(\ell)}$. Two ancestral lineages can therefore coalesce only when they sit in **different** individuals, and the two chromosomes of one individual descend from different parents.

**Scaling.** Take $\varepsilon_N = c/N^2$ and $r_N^{(\ell)} = r^{(\ell)}/N$ with $c > 0$ and $0 < r^{(\ell)} < \infty$, and measure time in units of $N^2$ steps.

**Limiting process.** On sample configurations in which all chromosomes are in distinct individuals ("completely dispersed"), define the continuous-time Markov chain $\xi(t)$ with jump rates

- **pair merger** of two lineages at rate $1 + c\,\frac{\psi^2}{4}\,C_{\beta;2;\beta-2}$;
- **recombination** of a lineage at crossover point $\ell$ at rate $r^{(\ell)}$;
- **group merger** at rate $c\,\frac{\psi^2}{4}\,C_{\beta;|J_1|,|J_2|,|J_3|,|J_4|;\,\beta - |J|}$. The lineages split into **at most four** groups $J_1, \dots, J_4$, each merging into one lineage, where at least one group has size $\ge 3$ or at least two groups have size $\ge 2$.

Here $\beta$ is the current number of active lineages, and for $s = b - k_1 - \dots - k_r \ge 0$

$$
C_{b;k_1,\dots,k_r;s} = \frac{4}{\psi^2}\sum_{l=0}^{s\wedge(4-r)} \binom{s}{l}\,\frac{(4)_{r+l}}{4^{k_1+\dots+k_r+l}}\,(1-\psi)^{s-l}\,\psi^{k_1+\dots+k_r+l},
$$

with $(4)_m = 4\cdot 3\cdots(4 - m + 1)$ the falling factorial.

**Theorem (convergence to the diploid ARG).** Let $\xi^{n,N}(m)$ be the ancestral process of $n$ sampled chromosomes. Under the scaling above,

$$
\big\{\xi^{n,N}(\lfloor N^2 t\rfloor)\big\}_{t>0} \longrightarrow \{\xi(t)\}_{t>0} \qquad (N \to \infty)
$$

in finite-dimensional distributions on $(0, \infty)$. The limit starts from the complete dispersion $\mathsf{cd}(\xi^{n,N}(0))$, in which chromosomes sharing an individual are first separated into distinct individuals.

**Theorem (general offspring laws).** The same limit holds, after rescaling time by $4/c_N$ with $c_N$ the pair coalescence probability, for general exchangeable diploid offspring laws satisfying Sagitov-type conditions for convergence to $\Xi$-coalescents and a matching recombination scaling. The limit is then a $\Xi$-ancestral recombination graph whose mergers are again restricted to at most four simultaneous groups.

## Expansion

Two timescales separate. Within one individual, the two chromosomes are scattered to two different parents in the next generation that involves them, which happens on the fast scale of order $N$ steps; at the slow scale $N^2$ the sample is therefore always completely dispersed. A matrix lemma formalizes this: if $A_N^r \to P$ (the projection onto dispersed states) for $r \gg N$, then $(A_N + cN^{-2}B)^{\lfloor tN^2\rfloor} \approx (P + cN^{-2}PBP)^{\lfloor tN^2\rfloor} \to e^{tG}$, extending Möhle's two-timescale theorem. In a large event, each lineage independently is an offspring with probability $\psi$ and then picks one of the four parental chromosomes (two parents, two chromosomes each) uniformly, which produces up to four simultaneous merging groups and the combinatorial factor in $C$. Diploidy thus turns a $\Lambda$-type sweepstakes mechanism into a $\Xi$-coalescent with simultaneous multiple mergers, and with recombination it yields an ancestral recombination graph whose correlations across loci differ from the Kingman ARG.

## Sources

- Matthias Birkner, Jochen Blath and Bjarki Eldon, "An ancestral recombination graph for diploid populations with skewed offspring distribution", arXiv (2012), model section and scaling relations, Definition 1 (limiting multilocus diploid ARG and the rates $C_{b;k_1,\dots,k_r;s}$), Theorem 2 (convergence), Theorem 3 (general offspring laws), appendix Proposition 4 and Lemmas 5 and 7, <https://doi.org/10.48550/arXiv.1203.4950>.
- M. Möhle, "A convergence theorem for Markov chains arising in population genetics and the coalescent with selfing", Advances in Applied Probability 30 (1998), 493–512, <https://doi.org/10.1239/aap/1035228080>.
