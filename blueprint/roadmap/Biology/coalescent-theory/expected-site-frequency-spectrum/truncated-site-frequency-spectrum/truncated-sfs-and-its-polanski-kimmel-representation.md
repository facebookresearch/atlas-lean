# Truncated site frequency spectrum and its Polanski–Kimmel representation

Let $(\Pi^n_t)_{t\ge0}$ be Kingman's coalescent on $n$ leaves in which each pair of blocks merges at rate $\alpha(t)$ at backward time $t$ ($1/\alpha$ is the population size history), with infinite-sites mutations at rate $\theta/2$ per lineage. Fix $\tau \in (0,\infty]$ and let $\mathcal K^\tau$ be the set of leaves below the mutations that occur in $[0,\tau)$. The **truncated SFS** $\eta^\tau_n(k)$, $1\le k\le n$, is defined by

$$\mathbb P_n(|\mathcal K^\tau| = k) = \tfrac{\theta}{2}\,\eta^\tau_n(k) + o(\theta), \qquad \theta\to0;$$

equivalently $\eta^\tau_n(|K|)/\binom{n}{|K|} = \mathbb E_n\big[\int_0^\tau \mathbf 1\{K\in\Pi^n_t\}\,dt\big]$ is the expected branch length within $[0,\tau)$ subtending a given set $K$ of leaves. For $k < n$, $\eta^\infty_n(k)$ is the usual expected SFS; $\eta^\tau_n(n)$ counts mutations above the root but within $[0,\tau)$.

**Theorem.**

1. (Whole-sample entry.) $\displaystyle \eta^\tau_n(n) = \tau - \sum_{k=1}^{n-1}\frac{k}{n}\,\eta^\tau_n(k).$
2. (Sample-size recurrence.) For $1\le k\le\nu$,

$$\eta^\tau_\nu(k) = \frac{\nu-k+1}{\nu+1}\,\eta^\tau_{\nu+1}(k) + \frac{k+1}{\nu+1}\,\eta^\tau_{\nu+1}(k+1).$$

3. (Truncated Polanski–Kimmel formula.) For $1\le k\le n-1$,

$$\eta^\tau_n(k) = \sum_{m=2}^n W_{n,k,m}\,c^\tau_m, \qquad c^\tau_m = \int_0^\tau \exp\Big[-\binom m2\int_0^t\alpha(x)\,dx\Big]\,dt,$$

with the universal constants $W_{n,k,2} = \frac{6}{n+1}$, $W_{n,k,3} = \frac{30(n-2k)}{(n+1)(n+2)}$ and, for $2\le m\le n-2$,

$$W_{n,k,m+2} = -\frac{(1+m)(3+2m)(n-m)}{m(2m-1)(n+m+1)}\,W_{n,k,m} + \frac{(3+2m)(n-2k)}{m(n+m+1)}\,W_{n,k,m+1}.$$

Hence all $\eta^\tau_n(k)$, $k<n$, are computable in $O(n^2)$ time, and $c^\tau_m = \mathbb E_m[\min(T_m,\tau)]$ for the first coalescence time $T_m$ of $m$ lineages.

4. (Conditioning on surviving lineages, constant size.) If $\alpha(t) \equiv \alpha$ on $[0,\tau)$, $a > 0$ and $0 < k \le n-a$, then the expected branch length subtending $k$ leaves given $a$ ancestral lineages at time $\tau$ that do not carry the mutation is

$$\eta^\tau_n(k\mid a) = \frac{2}{\alpha k}\,\frac{\binom{n-a}{k}}{\binom{n-1}{k}}.$$

## Depends on

- [Expected site frequency spectrum under variable population size](../../site-frequency-spectrum-under-variable-populatio/variable-sfs.md)

## Expansion

Item 1: within $[0,\tau)$ every leaf has ancestral branches of total length $\tau$, so summing branch lengths weighted by the number of leaves below them gives $\sum_{k\le n} k\,\eta^\tau_n(k) = n\tau$. Item 2 is sampling consistency of Kingman's coalescent: a sample of $\nu$ leaves is obtained from one of $\nu+1$ by deleting a uniform leaf, which keeps a branch subtending $k$ of the $\nu+1$ leaves at size $k$ with probability $(\nu+1-k)/(\nu+1)$ and turns a branch subtending $k+1$ into one subtending $k$ with probability $(k+1)/(\nu+1)$. Item 3 follows because the Polanski–Kimmel derivation of $\eta_n(k)$ is linear in the expected holding times, and truncation at $\tau$ only replaces each $\mathbb E_m[T_m]$ by $\mathbb E_m[T_m\wedge\tau]$. The truncated SFS feeds a dynamic program over a tree of population splits, implemented with a forward-in-time Moran model to keep the computation numerically stable for large samples and many populations.

## Sources

- John A. Kamm, Jonathan Terhorst, Yun S. Song, "Efficient computation of the joint sample frequency spectra for multiple populations", *Journal of Computational and Graphical Statistics* 26 (2017), 182–194, <https://doi.org/10.1080/10618600.2016.1159212>; preprint arXiv:1503.01133, <https://doi.org/10.48550/arXiv.1503.01133>. Numbering of the arXiv version: Section 2.2 (truncated coalescent and SFS), Lemmas 1–3, Proposition 1, Section 3.2 (Moran-based dynamic program).
