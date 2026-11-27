# Asymptotic cost of batched synthesis of random DNA strands

**Setting.** Fix a strand length $n$ and a strand universe $\mathcal U$: either all of $\{A,C,G,T\}^n$ (unconstrained strands) or the strands with no two equal consecutive bases (strands without homopolymers). Let $\mathcal S$ be a pool of $M$ strands drawn i.i.d. uniformly from $\mathcal U$. For a batch $\mathcal B$, $\operatorname{cost}(\mathcal B)$ is the length of a shortest common supersequence of the strands in $\mathcal B$ (the shortest reference strand that prints them all). For $k\mid M$ the synthesis cost of the pool is

$$\operatorname{cost}(\mathcal S)=\min_{\mathcal B_1\sqcup\cdots\sqcup\mathcal B_k=\mathcal S,\ |\mathcal B_i|=M/k}\ \sum_{i=1}^k\operatorname{cost}(\mathcal B_i).$$

**Upper bound.** There are absolute constants $C_1>0$ and $C_2<\infty$ such that, for $3\le k\le\frac14\sqrt{M/\log M}$, an efficiently computable partition into $k$ equal batches satisfies, with probability at least $1-1/M$,

$$\sum_{i=1}^k\operatorname{cost}(\mathcal B_i)\le 2nk-C_1k\sqrt n\quad\text{(no homopolymers)},\qquad \sum_{i=1}^k\operatorname{cost}(\mathcal B_i)\le 2.5nk+C_2\sqrt{n\log M}\quad\text{(unconstrained)}.$$

**Lower bound.** Let $M\ge10n^2\log n$ and $k\le\frac1{10}\sqrt{\log M/\log\log M}$. For strands without homopolymers there is an absolute constant $c_1<\infty$ such that, with probability at least $1-c_1/M$, every partition into $k$ equal batches has total cost at least $2nk-c_1k\sqrt{n\log k}$. For unconstrained strands with $M\le e^n$ there is an absolute constant $c_2>0$ such that, with probability at least $1-c_2^{-1}/M$, every such partition has total cost at least $2.5nk+c_2\sqrt{n\log M}$.

**Consequence.** For $k$ and $M$ in the ranges of both bounds ($3\le k\le\frac1{10}\sqrt{\log M/\log\log M}$ and $M\ge10n^2\log n$, with $M\le e^n$ for unconstrained strands), with probability $1-O(1/M)$: for unconstrained strands $\operatorname{cost}(\mathcal S)=2.5nk+\Theta(\sqrt{n\log M})$, so batching only removes a factor $k$ from the deviation term of a random partition; without homopolymers $2nk-c_1k\sqrt{n\log k}\le\operatorname{cost}(\mathcal S)\le2nk-C_1k\sqrt n$, so the cost falls *below* the main term by a deviation of order $k\sqrt n$ up to $\sqrt{\log k}$.

## Proof depends on

- [Reverse reference strand symmetry of DNA synthesis cost](reverse-reference-strand-symmetry-of-synthesis-cost.md)

## Expansion

For a single batch the periodic reference $(ACGT)^*$ prints a random strand at a cost that is a sum of $n$ independent uniform waiting times (uniform on $\{1,2,3,4\}$, or on $\{1,2,3\}$ after the first base without homopolymers), giving $2.5n+O(\sqrt{n\log M})$ and $2n+O(\sqrt{n\log M})$, and a stochastic-domination comparison of random walks shows no reference does asymptotically better. The batched upper bound combines two ideas: assign each strand the cheaper of $(ACGT)^*$ and its reverse, and then batch by quantiles of the per-strand cost, so that the cheapest $M/k$ strands share a batch, the next $M/k$ the next one, and so on. The lower bound is the technical core: it controls, uniformly over all partitions, how much a common supersequence can save over the strands' individual costs.

## Sources

- Konstantin Makarychev, Miklos Z. Racz, Cyrus Rashtchian and Sergey Yekhanin, "Batch Optimization for DNA Synthesis", IEEE Transactions on Information Theory 68 (2022), 7454–7470, <https://doi.org/10.1109/tit.2022.3184903>; numbering as in arXiv:2011.14532: Theorem 1.2 (upper bounds), Theorem 1.3 (lower bounds), Section 3 (single-batch bounds, Theorems 3.1–3.6) and Section 5 (multi-batch upper bound, Lemma 5.1).
