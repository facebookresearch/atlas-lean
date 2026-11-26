# IBD segment length distribution in a constant-size population

Two haploid genomes are sampled from a Wright–Fisher population of constant haploid size $N_e$, with time measured continuously in generations, so that the time $t$ to their most recent common ancestor (MRCA) at a site has density $N_e^{-1}e^{-t/N_e}$. Given $t$, the two lineages are separated by $2t$ meioses, so in the absence of interference the distance (in cM) from the site to the first recombination on either side is exponential with rate $t/50$ per cM, and the length $L$ of the shared non-recombinant segment spanning the site is Erlang-2 with rate $t/50$.

1. **Length spanning a site.** $L$ has density and interval probabilities

$$p(l) = \frac{100 N_e^2\, l}{(50 + l N_e)^3}, \qquad \int_u^v p(l)\,dl = \frac{100 N_e^2 (v - u)\bigl[25(u + v) + uvN_e\bigr]}{(50 + uN_e)^2 (50 + vN_e)^2}, \tag{4}$$

and $\int_u^\infty p(l)\,dl = \dfrac{100(25 + N_e u)}{(50 + N_e u)^2}$. By linearity of expectation, (4) is also the expected fraction of the genome covered by shared segments with length in $[u, v]$.

2. **Length of a segment.** Size-biasing removes the factor $l$: the length $s$ of a shared segment has density

$$p(s = l) = \frac{2 \cdot 50^2 N_e}{(50 + lN_e)^3}, \qquad \mathbb P(s \in [u, v]) = 50^2\bigl[(50 + N_e u)^{-2} - (50 + N_e v)^{-2}\bigr], \tag{10, 11}$$

with conditional mean $\mathbb E[s \mid s \in [u, v]] = \dfrac{50v + 2u(25 + N_e v)}{100 + N_e(u + v)}$; for $v = \infty$ this is $50/N_e + 2u$.

3. **Estimator.** If $\hat p_{[u, \infty)}$ is the observed fraction of genome shared through segments longer than $u$, averaged over pairs, solving $\hat p = 100(25 + N_e u)/(50 + N_e u)^2$ for $N_e$ gives a closed-form estimate of the population size.

## Expansion

$p(l) = \int_0^\infty N_e^{-1} e^{-t/N_e} (t/50)^2\, l\, e^{-tl/50}\, dt = \frac{2l}{2500 N_e}\bigl(\tfrac{1}{N_e} + \tfrac{l}{50}\bigr)^{-3}$, which simplifies to the stated density; it integrates to $1$ on $(0, \infty)$. A site falls in a segment with probability proportional to the segment's length, so dividing $p(l)$ by $l$ and normalizing gives the segment-length density; integrating it and $l$ times it over $[u, v]$ gives (11) and the conditional mean.

## Sources

- P. F. Palamara, T. Lencz, A. Darvasi and I. Pe'er, *Length distributions of identity by descent reveal fine-scale demographic history*, Am. J. Hum. Genet. 91 (2012), 809–822, <https://doi.org/10.1016/j.ajhg.2012.08.030>, PMCID PMC3487132 (Material and Methods, equations (3), (4), (10)–(13), (19); Appendix B).
