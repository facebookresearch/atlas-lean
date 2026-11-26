# Exact likelihood of sampled Moran genealogies

**Setting.** Run the stationary [Moran genealogy process](stationary-law-of-the-moran-genealogy-process.md) of size $n$ and event rate $\mu$, and sample one living individual at each of the times $t_1<t_2<\dots$. The observed chain $\mathcal{G}_1,\mathcal{G}_2,\dots$ records the genealogy of the samples taken so far; sample $k$ attaches to $\mathcal{G}_{k-1}$ at an attachment time $a_k$. Attachment may happen at a branch point of positive length (coalescence) or exactly at an earlier sampling time $t_i$ (sample $i$ is a direct ancestor of sample $k$). Let $\ell_k(t)$ be the number of lineages of $\mathcal{G}_k$ at time $t$, and $\mathrm{live}(\mathcal{G}_k)$ the set of samples with no later sample attached at their own time, $r=|\mathrm{live}(\mathcal{G}_k)|$.

**Theorem (conditional attachment).** Given $\mathcal{G}_k$, with $\mathrm{live}(\mathcal{G}_k)=\{e_1<\dots<e_q\}$,
$$-\log\mathbb{P}(A_{k+1}<a\mid\mathcal{G}_k)=\int_a^\infty\frac{\ell_k(t)}{\binom n2}\,\mu\,dt+\sum_{j:\,a\le e_j}\log\frac{n-\ell_k(e_j)}{n-\ell_k(e_j)-1},$$
and the conditional law of the attachment time has a density part $\frac{\mu\,\ell_k(a)}{\binom n2}$ and point masses $\frac{1}{n-\ell_k(a)}$ at live sample times, each multiplied by $\mathbb{P}(A_{k+1}\le a\mid\mathcal{G}_k)$.

**Corollary (log-likelihood).** For $k>1$,
$$\log\mathcal{L}=(r-k)\log n+(r-1)\log\frac{\mu}{\binom n2}-\int_{-\infty}^{\infty}\frac{\binom{\ell_k(t)}{2}}{\binom n2}\,\mu\,dt+\sum_{e\in\mathrm{live}(\mathcal{G}_k)}\log\Bigl(1-\frac{\ell_k(e)}{n}\Bigr).$$

As $n\to\infty$ with $\mu/\binom n2$ fixed, genealogies with direct ancestry ($r<k$) receive vanishing likelihood and the remaining terms reduce to the serially sampled coalescent likelihood; for finite $n$, direct ancestry among samples has positive probability and the coalescent likelihood is not exact.

## Depends on

- [Stationary law of the Moran genealogy process](stationary-law-of-the-moran-genealogy-process.md)

## Expansion

Trace the new sample's lineage backward from $t_{k+1}$. Between sampling times it merges with one of the $\ell_k(t)$ existing lineages when a Moran birth has its parent on that lineage and its child on the new lineage, which happens at rate $\mu\,\ell_k(t)/\binom n2$; integrating gives the exponential term. At a live sample time $e_j$ the new lineage can pass through the sampled individual itself (direct descent), which produces the logarithmic correction and the point masses with weight $1/(n-\ell_k(e_j))$. Multiplying the conditional densities over $k$ and collecting terms gives the joint density of the chain and the log-likelihood.

## Sources

- A. A. King, Q. Lin, E. L. Ionides, "The Sampled Moran Genealogy Process", arXiv:2002.11184 (2020), the definition of the lineage-count function $\ell_k$, Theorem 3, Corollary 6, Theorem 9 and Corollary 10, <https://doi.org/10.48550/arXiv.2002.11184>.
