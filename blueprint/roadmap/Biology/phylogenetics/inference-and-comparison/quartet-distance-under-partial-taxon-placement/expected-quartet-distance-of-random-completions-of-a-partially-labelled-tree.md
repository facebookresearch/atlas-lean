# Expected quartet distance of random completions of a partially labelled tree

**Setting.** A phylogenetic tree $T$ of order $n$ is an unrooted tree with $n$ leaves whose internal vertices have degree 3. A labelling assigns the taxa $[n]$ bijectively to the leaves; a labelled tree displays exactly $\binom n4$ quartets $[ab|cd]$ (the induced topology on each four-taxon set). The **quartet distance** $qd(T_1,T_2)$ of two labelled trees is $\binom n4$ minus the number of quartets displayed by both. For uniformly random labellings of a fixed shape, $\mathbb{E}[qd] = \frac23\binom n4$ by linearity, since each four-taxon set receives one of its three quartets uniformly.

**Partial information.** Fix $S\subseteq\mathcal{L}(T)$ with $|S| = k = \alpha n$ and a labelling $T(S)$ of $S$ by taxa $[k]$; a *completion* places the remaining $n-k$ taxa on $\mathcal{L}(T)\setminus S$. Let $X_{T(S)} = qd(T_1,T_2)$ for two independent uniform completions, and

$$minexp(n,\alpha) = \min_{T}\min_{|S| = \alpha n}\mathbb{E}[X_{T(S)}], \qquad maxexp(n,\alpha) = \max_T\max_{|S|=\alpha n}\mathbb{E}[X_{T(S)}].$$

**Exact formula.** Split quartets by the number $i$ of pinned taxa they contain. Types $i=0,1$ contribute $\frac23$ each, type 4 contributes 0, and

$$\mathbb{E}[X_{T(S)}] = \tfrac23\tbinom{n-k}{4} + \tfrac23 k\tbinom{n-k}{3} + \tbinom{n-k}{2}\sum_{\{a,b\}\subseteq[k]}\bigl(2p_{a,b} - \tfrac32p_{a,b}^2\bigr) + 2(n-k)\sum_{\{a,b,c\}\subseteq[k]}\bigl(p_{ab|c}p_{ac|b} + p_{ab|c}p_{bc|a} + p_{ac|b}p_{bc|a}\bigr),$$

where $p_{a,b}$ is the fraction of pairs of free leaves that would separate $a$ from $b$ in the induced quartet, and $p_{ab|c}$ is the fraction of free leaves $x$ inducing $[ab|cx]$ (so $p_{ab|c}+p_{ac|b}+p_{bc|a}=1$).

**Theorem (minimum).** For every $1\le k\le n-1$, $minexp(n,k/n) = \frac23\binom{n-k}{4} + \frac23 k\binom{n-k}{3}$, attained when $S$ is the leaf set of one side of a split (an internal edge) of $T$; hence

$$minexp(n,\alpha) = \Bigl(\tfrac23(1-\alpha)^4 + \tfrac83\alpha(1-\alpha)^3\Bigr)\tbinom n4\,(1+o(1)), \qquad minexp(n,\tfrac12) = \tfrac{5}{24}\tbinom n4(1+o(1)).$$

**Theorem (maximum expectation).**

$$\Bigl(\tfrac23 - \tfrac{653\alpha^4 + 414\alpha^3 + 33\alpha^2}{1650}\Bigr)\tbinom n4 + o(n^4) \;\ge\; maxexp(n,\alpha) \;\ge\; \Bigl(\tfrac23 - \tfrac{10\alpha^4 + 32\alpha^3 + 12\alpha^2}{81}\Bigr)\tbinom n4 + o(n^4),$$

so $0.606\binom n4 \gtrsim maxexp(n,\frac12)\gtrsim 0.572\binom n4$. The simpler bound $(\frac23 - \frac23\alpha^4)\binom n4$ from the exact formula is not tight.

## Depends on

- [Four-taxon subsets](../../quartet-support-and-determination-of-trees-by-qu/quartets.md)

## Proof sketch

Fix one completion and randomize the other. A type-1 quartet $[ax|yz]$ is matched with probability $\frac13$ given the three free leaves, by symmetry. For a type-2 pair $a,b$: a quartet $[ab|xy]$ fails with probability $p_{a,b}$, and $[ax|by]$ fails with probability $1 - p_{a,b}/2$; summing over the $N_{a,b} = p_{a,b}\binom{n-k}{2}$ separating pairs gives $\binom{n-k}{2}(2p_{a,b} - \frac32 p_{a,b}^2)$. Type-3 terms are handled the same way. Both $p$-penalties are non-negative and vanish exactly when every $p_{a,b}=0$ and every triple has one of its $p_{ab|c}$ equal to 1, which happens when $S$ hangs off one internal edge: then the pinned taxa always sit together on one side of every quartet that involves free taxa. Upper bounds for $maxexp$ come from bounding the two penalty sums from below over all trees, via linear and non-linear optimization.

## Sources

- Sagi Snir, Osnat Weissberg and Raphael Yuster, "On the quartet distance given partial information", *Journal of Graph Theory* 100 (2022), 252–269, <https://doi.org/10.1002/jgt.22776>. Preprint version: arXiv:2111.13101 (2021), Section 2 (Definition 2.1, Theorems 2.2 and 2.3), Section 3 (formula for the expectation and proof of Theorem 2.2), Section 4, <https://doi.org/10.48550/arXiv.2111.13101>.
