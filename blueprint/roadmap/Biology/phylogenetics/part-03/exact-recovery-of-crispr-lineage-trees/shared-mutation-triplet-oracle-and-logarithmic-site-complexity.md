# Shared-mutation triplet oracle and logarithmic site complexity

**Model.** Let $\mathcal T$ be a rooted binary ultrametric tree with $n$ leaves (sampled cells) and root-to-leaf distance $1$. Each of $k$ characters (recording sites) starts unedited at the root and mutates at most once along any lineage, after an $\mathrm{Exp}(\lambda)$ waiting time, so a mutation occurs on the path from the root to $u$ with probability $1 - e^{-\lambda\,\mathrm{dist}(r,u)}$; the new state $j \in \{1,\dots,m\}$ has probability $q_j$, it is inherited and never changes, and characters are independent. Let $q = \sum_j q_j^2$ (probability that two independent mutations coincide) and let each leaf character be missing independently with probability $p_d$. For leaves $u,v$ let $s(u,v)$ be the number of shared mutations. A triplet $(a,b\,|\,c)$ means $c$ is the outgroup.

**Expected gap.** If $(a,b\,|\,c)$ has $\mathrm{depth}(\mathrm{LCA}(a,b,c)) = d$, $\mathrm{dist}(\mathrm{LCA}(a,b,c),\mathrm{LCA}(a,b)) \ge \ell^*$ and $\lambda\ell^* \le 1$, then without missing data

$$\mathbb E[s(a,b) - s(b,c)] \ \ge\ k\,\lambda\ell^*\,\delta(d),\qquad \delta(d) = 0.6\big(e^{-\lambda d}(1-q) + q\,e^{-\lambda(2-d)}\big).$$

**Oracle.** With $\delta^* = \min_{x\in[0,d^*]}\delta(x)$ and threshold $t = \tfrac12 k\lambda\ell^*\delta^*$, return $c$ if $s(a,b) - \max(s(a,c),s(b,c)) > t$ and Null otherwise.

**Theorem.** If

$$k \ \ge\ \max\left(\frac{(96\log n + 32\log(1/\zeta))\,q}{\ell^{*2}\,\delta^{*2}},\ \frac{(96\log n + 32\log(1/\zeta))\,(\ell^* + (1 - e^{-\lambda})q)}{0.6\,\lambda\,\ell^{*2}\,\delta^*\,(1 - q + q e^{-2\lambda})}\right),$$

then with probability at least $1 - \zeta$ the oracle never returns a wrong outgroup for triplets rooted at depth at most $d^*$ and returns the correct one whenever the triplet is $\ell^*$-separated; triplet-based (Aho-type) reconstruction then recovers $\mathcal T$ up to depth $d^*$ in polynomial time. With missing data the same holds with $t$ scaled by $(1-p_d)^3$ and the two terms of the bound divided by $(1-p_d)^5$ and $(1-p_d)^3$.

**Corollaries.** For constant $\lambda$ and state distribution, with $\mathcal T$ of minimum edge length $\ell$ and $\lambda\ell \le 1$, exact recovery of the whole tree with high probability needs

$$k = O\Big(\frac{\log n}{\ell^2}\Big)\ \text{characters, and } k = O\Big(\frac{\log n}{\ell^2(1-p_d)^3}\Big) \text{ with missing data};$$

without a minimum edge length, all $\ell^*$-separated triplets are resolved with $k = O(\log n/\ell^{*2})$; and if all edge lengths lie between $\ell$ and $O(\ell)$, a bottom-up algorithm with a sufficiently low mutation rate needs only $k = O(\log n/\ell)$.

## Depends on

- [Rooted triplet](../../splits-compatibility-ultrametrics-and-upgma/triplet.md)

## Expansion

Mutations above $\mathrm{LCA}(a,b,c)$ are shared by all three leaves and cancel in $s(a,b) - s(b,c)$. A character contributes to $s(a,b)$ after the split either through one mutation on the internal edge toward $\mathrm{LCA}(a,b)$ or through homoplasy (two independent identical mutations), whereas it contributes to $s(b,c)$ only through homoplasy, with probability $e^{-\lambda d}(1 - e^{-\lambda(1-d)})^2 q$; subtracting and using $0.6x \le 1 - e^{-x} \le x$ on $[0,1]$ gives the gap. Monotonicity of the success probability in the separation reduces to the worst case, and Chernoff bounds for binomial counts plus a union bound over the $O(n^3)$ triplets produce the $\log n$ factor. These bounds match the $O(\log n/\ell^2)$ guarantees known for the two-state Cavender–Farris–Neyman model despite irreversibility, many states and missing data.

## Sources

- R. Wang, R. Zhang, A. Khodaverdian, N. Yosef, "Theoretical guarantees for phylogeny inference from single-cell lineage tracing", Proceedings of the National Academy of Sciences USA 120:e2203352120 (2023), generative model, Definitions 1–2, Corollaries 1–4, Lemmas 1–3, Theorems 1–3, <https://doi.org/10.1073/pnas.2203352120>, PMCID PMC10041172.
