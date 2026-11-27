# Reverse reference strand symmetry of DNA synthesis cost

**Setting.** In array-based DNA synthesis, all strands of a batch are grown in parallel by following a common *reference strand* $R$ over the alphabet $\{A,C,G,T\}$: at each step the next base of $R$ is appended to a chosen subset of the strands, so every synthesized strand must be a subsequence of $R$. For a strand $S=s_1\cdots s_n$ and an infinite periodic reference $R$, let $\operatorname{cost}_R(S)$ be the length of the shortest prefix of $R$ that contains $S$ as a subsequence (greedy earliest embedding). A strand has *no homopolymers* if $s_i\ne s_{i+1}$ for all $i$.

**Statement.** Let $\widetilde R=(ACGT)^*$ and let $\overline R=(TGCA)^*$ be its reverse. For every strand $S\in\{A,C,G,T\}^n$ without homopolymers,

$$\operatorname{cost}_{\widetilde R}(S)+\operatorname{cost}_{\overline R}(S)=4n+1,$$

so the better of the two references prints $S$ with cost at most $2n$. Moreover the base complement $\varphi$ ($A\leftrightarrow T$, $C\leftrightarrow G$) is a bijection of $\{A,C,G,T\}^n$ with $\operatorname{cost}_{\widetilde R}(S)+\operatorname{cost}_{\widetilde R}(\varphi(S))=4n+1$ for every homopolymer-free $S$.

## Expansion

Split the cost into per-character waiting times: $X_1$ is the position of $s_1$ in one period of $R$ ($1\le X_1\le4$), and for $i\ge2$, $X_i$ is the cyclic distance from $s_{i-1}$ to $s_i$ along $R$, which lies in $\{1,2,3\}$ when $s_i\ne s_{i-1}$. Reversing the cyclic order turns a forward distance $k\in\{1,2,3\}$ into $4-k$ and a starting position $k$ into $5-k$, so the per-character costs under $\widetilde R$ and $\overline R$ add to $4$ for $i\ge2$ and to $5$ for $i=1$; summing gives $4n+1$. Complementing both the strand and the reference leaves the cost unchanged and maps $\widetilde R$ to $\overline R$, which gives the bijection statement. For uniformly random homopolymer-free strands, the cost under $(ACGT)^*$ is a sum of independent uniform steps with mean close to $2n$; choosing per strand the cheaper of the two references reflects this sum about $2n$, and this is the first of two ideas behind the batched upper bound.

## Sources

- Konstantin Makarychev, Miklos Z. Racz, Cyrus Rashtchian and Sergey Yekhanin, "Batch Optimization for DNA Synthesis", IEEE Transactions on Information Theory 68 (2022), 7454–7470, <https://doi.org/10.1109/tit.2022.3184903>; numbering as in arXiv:2011.14532: Section 1.2 and Lemma 5.1 (the lemma's display names the reverse reference with a transposed letter pair; the reverse of $ACGT$ used in Section 1.2 is $TGCA$).
