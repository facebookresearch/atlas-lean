# Percolating neutral networks of combinatory maps

Let $\vartheta_{\mathcal H}:Q_4^n\to\{\text{shapes}\}$ be the [combinatory sequence-to-shape map](combinatory-sequence-to-shape-maps-and-large-preimages.md) for the pairing relation $\mathcal R^\dagger$ and the cycle base graph $\mathcal H$, and let $\mu_\pm=\frac{1\pm\sqrt5}{2}$. The *neutral network* of a shape $\mathcal S$ is its preimage $\vartheta_{\mathcal H}^{-1}(\mathcal S)$, viewed as an induced subgraph of the sequence space $Q_4^n$; a *neutral neighbor* of a sequence is an adjacent sequence (one point mutation away) with the same shape.

**Theorem (neutral networks).** There are at least $(\sqrt2)^{\,n-1}$ shapes $\mathcal S$ such that

1. the set of sequences mapping into $\mathcal S$ has a connected component of size at least $\mu_+^{\,n}+\mu_-^{\,n}$ (which exceeds $(\sqrt2)^{n}$);
2. the set of sequences mapping into $\mathcal S$ percolates: it has diameter $n$, so it contains sequences differing in every position.

**Theorem (neutral neighbors).** For a shape $\mathcal S_M$ of the cycle base graph on $2k$ positions, where $M\subset\{1,\dots,k\}$ indexes its isolated nucleotides, let $\lambda_{\mathcal S_M}(m)$ be the number of sequences folding into $\mathcal S_M$ that have exactly $m$ neutral neighbors. Then $\lambda_{\mathcal S_M}(m)\ge\lambda_{C_{2k}}(m)$ for all $m$, where $C_{2k}$ is the full cycle shape, and the bivariate generating function $\sum_{k\ge2}\sum_m\lambda_{C_{2k}}(m)x^my^{2k}$ is an explicit rational function, computed by the transfer-matrix method.

## Expansion

Neutral networks (large connected sets of sequences sharing a structure and spanning sequence space) are the combinatorial basis of the neutral theory of molecular evolution: populations can drift through sequence space without losing structure. For RNA secondary structures their existence is supported only by random-graph models and exhaustive enumeration for $n\le20$. For combinatory maps on the cycle base graph the proof is constructive: it exhibits explicit mutation paths inside the preimage, for instance from $(\mathbf C,\mathbf D,\mathbf C,\mathbf D)$ to its antipode $(\mathbf B,\mathbf A,\mathbf B,\mathbf A)$ for the full $4$-cycle shape, and the component sizes grow like the Lucas numbers $\mu_+^n+\mu_-^n$. A random-graph version (base graph $G_{n,p}$ with $p=(1-\epsilon)/n$) yields, with high probability, at least $\beta^n$ such shapes for any $\beta<\sqrt2$, with diameter $n-\omega_n$.

## Depends on

- [Combinatory sequence-to-shape maps and their large preimages](combinatory-sequence-to-shape-maps-and-large-preimages.md)

## Sources

- Emma Y. Jin, Jing Qin, Christian M. Reidys. *Neutral Networks of Sequence to Shape Maps* (2007), Sections 2–4: Lemmas 1–2 and Theorems 1–2. <https://doi.org/10.48550/arXiv.0706.0760>
