# Repeat-bridging conditions for greedy and de Bruijn assembly

Use the repeat, triple-repeat, interleaving and bridging notions of the bridging form of Ukkonen's condition, and let $\ell_{\mathrm{repeat}}$ be the length of the longest repeat of $s$. The $K$-mer (de Bruijn) graph of a set of strings has a node for each distinct $K$-mer and an edge between $K$-mers adjacent in some string; condensing unambiguous paths gives the **condensed sequence graph**. An **X-node** has in- and out-degree at least $2$; a **2-X-node** is traversed exactly twice by the cycle spelling $s$.

**Theorem 2 (greedy).** The algorithm that repeatedly merges the two fragments with longest suffix–prefix overlap reconstructs $s$ if every repeat is bridged.

**Theorem 3 (spectrum).** Let $G$ be the condensed sequence graph of the $K$-mer graph built from the $(K+1)$-spectrum of $s$. If $s$ has no triple repeat and no interleaved repeat pair of length at least $K$, then $G$ has a unique Eulerian cycle, and it spells $s$.

**Theorem 4 (basic de Bruijn).** Building the $K$-mer graph from the $(K+1)$-mers of the reads, condensing it and taking an Eulerian cycle reconstructs $s$ if (a) $K > \ell_{\mathrm{interleaved}}$, (b) $K > \ell_{\mathrm{triple}}$, and (c) adjacent reads overlap by at least $K$.

**Theorem 5 (simple bridging).** If, in addition, each bridged 2-X-node is split using its bridging read, reconstruction succeeds when (a) all interleaved repeats are bridged, (b) $K > \ell_{\mathrm{triple}}$, and (c) adjacent reads overlap by at least $K$.

**Coverage requirements.** With $a_m$ the number of repeats of length $m$ and $b_{m,n}$ the number of interleaved pairs of lengths $m, n$, union bounds give $\mathbb P[\text{some repeat unbridged}] \le \sum_m a_m (p_m^{\mathrm{unbridged}})^2$ and $\mathbb P[\text{some interleaved pair unbridged}] \le \sum_{m,n} b_{m,n} (p_m^{\mathrm{unbridged}})^2 (p_n^{\mathrm{unbridged}})^2$, while condition (c) forces normalized coverage $\bar c = c / c_{\mathrm{LW}} \ge 1/(1 - K/L)$.

## Depends on

- [Bridging form of Ukkonen's condition](bridging-form-of-ukkonens-condition.md)
- [De Bruijn graph genome assembly](../../de-bruijn-graph-genome-assembly/README.md)

## Expansion

Greedy merging can only err by joining across an unbridged repeat, so it needs $L > \ell_{\mathrm{repeat}} + 1$ and is suboptimal when $\ell_{\mathrm{repeat}} \gg \ell_{\mathrm{interleaved}}$ (for human chromosome 19, $4092$ versus $2248$). In the condensed graph, repeats appear as X-nodes; with no long interleaved or triple repeats, the order in which X-nodes are traversed is forced, giving a unique Eulerian cycle. Reducing $K$ lowers the overlap requirement (c), and splitting bridged two-copy repeats replaces condition (a) by the necessary bridging condition, so simple bridging is optimal for interleaved repeats and its remaining gap is due to triple repeats. When the read length slightly exceeds $L_{\mathrm{crit}}$, covering the genome already suffices, producing a sharp critical phenomenon in the feasible $(L, N)$ region.

## Sources

- G. Bresler, M. Bresler, D. Tse, "Optimal assembly for high throughput shotgun sequencing", BMC Bioinformatics 14 (Suppl 5) (2013) S18, Theorems 2–5 and Eqs. 5–7, <https://doi.org/10.1186/1471-2105-14-S5-S18>, PMCID PMC3706340.
