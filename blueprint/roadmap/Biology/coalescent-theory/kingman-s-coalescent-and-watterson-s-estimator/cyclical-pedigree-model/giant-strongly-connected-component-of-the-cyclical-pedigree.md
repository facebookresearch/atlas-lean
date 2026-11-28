# Giant strongly connected component of Wakeley's cyclical pedigree

**Model.** In a diploid monoecious population of $N$ individuals, a pedigree assigns to each individual two parents in the previous generation; genetic lineages are random walks that move from an individual to one of its two parents with probability $1/2$ each. Wakeley et al.'s **cyclical model** samples the parental relations once, each individual $i \in [N]$ choosing its two parents independently and uniformly from $[N]$ (one individual may be both parents), and reuses the same relations in every earlier generation. The pedigree is then a random directed multigraph $\mathrm{WCM}_N$ on $[N]$ with out-degree $2$ at every vertex. It has the law of the directed configuration model with out-degrees $d_i^+ = 2$ and in-degrees $(d_1^-, \dots, d_N^-) \sim \mathrm{Mult}(2N, 1/N)$.

Let $x^* \approx 0.797$ be the survival probability of a Galton–Watson tree with Poisson$(2)$ offspring, i.e. the positive root of $1 - x = e^{-2x}$.

**Theorem.**

1. $\mathrm{WCM}_N$ has a unique giant strongly connected component $S^N$ with $|S^N|/N \to x^*$ in probability.
2. With high probability: from every vertex $v \notin S^N$ there is a directed path into $S^N$ of at most $\frac{\log\log N}{\log 2}(1 + o(1))$ edges; no edge leaves $S^N$; the number of vertices reachable from $v$ without passing through $S^N$ is at most $\frac{2}{-\log(4x^*(1-x^*))}\log N\,(1 + o(1))$, and so is the size of the second largest strongly connected component.

**Corollary.** With high probability the simple random walk on $\mathrm{WCM}_N$ (the ancestral lineage) has a unique stationary distribution, supported on $S^N$.

So about $20\%$ of individuals lie outside the giant component, and every individual has an ancestral line entering $S^N$ within about $\log_2\log N$ generations (whereas a random ancestral lineage takes $O(\log N)$ generations, Remark 3.4, and still eventually enters the unique closed class $S^N$).

## Expansion

Exploring the in-neighborhood of a vertex (its ancestors) is approximately a branching process with Poisson$(2)$ offspring, while the out-neighborhood (its descendants through the reused pedigree) always grows by out-degree $2$; vertices with a large ancestral fan-in form the giant component, whose density is the survival probability $x^*$. Results of Cooper and Frieze for the directed configuration model give that any two large fan-in and fan-out sets intersect, so the giant component is unique and absorbing. The doubling of the out-neighborhood gives the $\log\log N/\log 2$ bound on entrance paths, and a subcritical exploration of the part of the graph outside the giant component yields the logarithmic bounds with constant $-\log(4x^*(1-x^*))$.

## Sources

- Jochen Blath, Stephan Kadow, Marcel Ortgiese, "The largest strongly connected component in Wakeley et al's cyclical pedigree model", published as "The largest strongly connected component in the cyclical pedigree model of Wakeley et al.", *Theoretical Population Biology* 98 (2014), 28–37, <https://doi.org/10.1016/j.tpb.2014.10.001>; preprint arXiv:1405.7276, <https://doi.org/10.48550/arXiv.1405.7276>. Numbering of the arXiv version: Section 2 (definitions, Proposition 2.1), Theorem 3.1, Corollary 3.3, Propositions 4.6 and 4.7.
