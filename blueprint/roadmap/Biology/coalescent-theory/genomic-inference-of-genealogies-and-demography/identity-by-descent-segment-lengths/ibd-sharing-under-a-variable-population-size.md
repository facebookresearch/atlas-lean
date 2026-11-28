# IBD sharing under a variable population size

Let the haploid population size be $N(g)$ in generation $g$ before the present, and suppose it is eventually constant: $N(g) = N_a$ for all $g > G$. Two haplotypes find their common ancestor in generation $g$ with probability

$$\mathbb P(g_{\mathrm{mrca}} = g) = \frac{1}{N(g)} \prod_{j=1}^{g-1}\Bigl(1 - \frac{1}{N(j)}\Bigr). \tag{5}$$

Given $g_{\mathrm{mrca}} = g$ the length of the shared segment spanning a site is Erlang-2 with rate $g/50$ per cM, independently of the demography. Hence the probability that a site is covered by a shared segment with length in $[u, v]$ is

$$\int_u^v p(l)\,dl = \phi_1 + \phi_2, \tag{6}$$

$$\phi_1 = \sum_{g=1}^{G} \Bigl(\prod_{j=1}^{g-1}\bigl(1 - \tfrac{1}{N(j)}\bigr)\Bigr)\frac{1}{N(g)} \int_u^v \mathrm{Erl}_2\bigl(l; \tfrac{g}{50}\bigr)\,dl,$$

$$\phi_2 = \frac{1}{N_a}\prod_{j=1}^{G}\Bigl(1 - \frac{1}{N(j)}\Bigr) \sum_{g=G+1}^{\infty}\Bigl(1 - \frac{1}{N_a}\Bigr)^{g-G-1} \int_u^v \mathrm{Erl}_2\bigl(l; \tfrac{g}{50}\bigr)\,dl,$$

a finite sum plus a geometric tail that admits a closed form in the continuous-time approximation. Any recent history $N(1), \dots, N(G)$, for instance exponential growth $N(t) = N_c e^{-rt}$ for $t \le G$ with $r = \ln(N_c/N_a)/G$, therefore gives an explicit expected sharing spectrum, which can be fitted to observed sharing in several length bins to infer the history. When $N(g) \equiv N_e$ this reduces, in continuous time, to the [constant-size distribution](ibd-segment-length-distribution-in-a-constant-size-population.md).

Treating the number of shared segments in a bin as approximately Poisson and independent of their lengths, the expected number of segments with length in $[u, v]$ in a genome of length $\gamma$ cM is $\lambda \approx \gamma \int_u^v p(l)\,dl \,/\, \mathbb E[s \mid s \in [u, v]]$.

## Depends on

- [IBD segment length distribution in a constant-size population](ibd-segment-length-distribution-in-a-constant-size-population.md)

## Expansion

Equation (5) is the probability that the two lineages fail to coalesce in each of generations $1, \dots, g-1$ and coalesce in generation $g$, with per-generation coalescence probability $1/N(j)$. Conditioning on $g_{\mathrm{mrca}}$ and splitting the sum at $G$ gives (6); after $G$ the coalescence probability is constant, so the tail is geometric.

## Sources

- P. F. Palamara, T. Lencz, A. Darvasi and I. Pe'er, *Length distributions of identity by descent reveal fine-scale demographic history*, Am. J. Hum. Genet. 91 (2012), 809–822, <https://doi.org/10.1016/j.ajhg.2012.08.030>, PMCID PMC3487132 (Material and Methods, equations (2), (5)–(7), (14); Appendix A).
