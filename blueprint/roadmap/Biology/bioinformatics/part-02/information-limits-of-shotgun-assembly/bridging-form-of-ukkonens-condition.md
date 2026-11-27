# Bridging form of Ukkonen's condition

Let $s$ be a DNA sequence of length $G$ and let $s_t^\ell$ be its length-$\ell$ substring starting at $t$. A **repeat** of length $\ell$ is a pair of positions $t_1 < t_2$ with $s_{t_1}^\ell = s_{t_2}^\ell$ that is maximal ($s(t_1 - 1) \ne s(t_2 - 1)$ and $s(t_1 + \ell) \ne s(t_2 + \ell)$); a **triple repeat** is defined likewise with three copies, not all extendable on either side. Two repeats at positions $(t_1, t_3)$ and $(t_2, t_4)$ are **interleaved** if $t_1 < t_2 < t_3 < t_4$ or $t_2 < t_1 < t_4 < t_3$. A read **bridges** a copy of a repeat if it covers the copy together with at least one flanking base on each side. Let $\ell_{\mathrm{interleaved}}$ be the length of the longest interleaved pair (the shorter of its two repeats) and $\ell_{\mathrm{triple}}$ the length of the longest triple repeat.

**Theorem.** Given $s$ and a set of reads, if some pair of interleaved repeats, or some triple repeat, has all its copies unbridged, then there is a different sequence $s'$ of the same length under which the likelihood of observing the reads is the same. Hence exact reconstruction with success probability above $1/2$ requires every interleaved pair and every triple repeat to be bridged, and in particular (Ukkonen's condition) the read length must satisfy

$$L > L_{\mathrm{crit}} := \max\{\ell_{\mathrm{interleaved}}, \ell_{\mathrm{triple}}\} + 1 .$$

**Coverage consequence.** With $N$ reads whose start points form a Poisson process of rate $N/G$, a given length-$\ell$ copy is unbridged with probability $p_\ell^{\mathrm{unbridged}} = e^{-\frac NG (L - \ell - 1)^+}$. Requiring error probability at most $\varepsilon$ on the longest interleaved pair gives

$$N \ge \frac{G}{L - \ell_{\mathrm{interleaved}} - 1}\,\ln\frac{1}{2\varepsilon}.$$

## Depends on

- [Lander–Waterman limit for the uncovered fraction](../../lander-waterman-coverage-model/tendsto-normalized-count-uncovered.md)
- [Poisson process](../../../../Probability/point-processes/poisson-processes/is-poisson-process.md)

## Expansion

If all copies of two interleaved repeats are unbridged, swapping the two segments lying between them yields $s'$ with exactly the same multiset of reads at the same likelihood; three unbridged copies of a triple repeat allow the analogous exchange. Since guessing between equally likely sequences fails with probability at least $1/2$, the bridging requirement is necessary for every assembler. Only the bridging status, not the repeat length itself, matters, which extends Ukkonen's sequencing-by-hybridization condition to random shotgun reads. Combined with Lander–Waterman's covering requirement $N_{\mathrm{LW}} \approx \frac GL \ln\frac{N_{\mathrm{LW}}}{\varepsilon}$, this produces a lower-bound curve with a vertical asymptote at $L = L_{\mathrm{crit}}$.

## Sources

- G. Bresler, M. Bresler, D. Tse, "Optimal assembly for high throughput shotgun sequencing", BMC Bioinformatics 14 (Suppl 5) (2013) S18, Section "Lower bounds", Eqs. 2–4 and Theorem 1, <https://doi.org/10.1186/1471-2105-14-S5-S18>, PMCID PMC3706340.
