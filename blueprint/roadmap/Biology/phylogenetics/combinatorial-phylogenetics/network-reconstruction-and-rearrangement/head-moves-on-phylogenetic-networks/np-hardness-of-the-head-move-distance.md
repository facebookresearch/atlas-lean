# NP-hardness of the head-move distance

**Problem.** Given two binary phylogenetic networks $N,N'$ on the same leaf set with the same number $k>0$ of reticulations, compute the *head-move distance* $d_{\mathrm{Head}}(N,N')$: the minimum number of head moves (relocations of the head of an edge, keeping the result a binary phylogenetic network) needed to turn $N$ into $N'$.

**Theorem.** Computing $d_{\mathrm{Head}}(N,N')$ is NP-hard.

**Key lemma (reduction).** For a rooted binary phylogenetic tree $T$ on $X$, $|X|=n$, let $\overline{T}$ be its *upside-down version*: reverse all edges of $T$, and glue the reversed copy at its leaves to a caterpillar on $X\cup\{y\}$ in which each pendant edge to $x\in X$ carries $2n$ extra pendant leaves $e_{x,1},\dots,e_{x,2n}$. Then for any two trees $T_1,T_2$ on $X$,

$$d_{\mathrm{rSPR}}(T_1,T_2)=d_{\mathrm{Head}}(\overline{T}_1,\overline{T}_2).$$

## Depends on

- [rSPR distance](../../../../not-yet-classified/rooted-spragreement-forest/rspr-dist.md)

## Proof depends on

- [rSPR DISTANCE is NP-complete](../../../../not-yet-classified/rooted-spragreement-forest/rspr-distance-np-complete.md)
- [rSPR distance equals the maximum agreement forest number](../../../../not-yet-classified/rooted-spragreement-forest/rspr-dist-eq-rooted-maf-number.md)

## Expansion

The reversed tree turns every internal tree node into a reticulation, so a head move in $\overline{T}$ acts on the reversed copy exactly as an rSPR move (prune and regraft) acts on $T$; this gives $d_{\mathrm{Head}}\le d_{\mathrm{rSPR}}$. For the converse, the $2n$ pendant leaves per label make the caterpillar part too expensive to touch: any head-move sequence shorter than $2n$ leaves an upside-down agreement forest of $\overline{T}_1,\overline{T}_2$ with at most one more component than the sequence length, and that forest yields a maximum agreement forest of $T_1,T_2$ of no larger size. Since $d_{\mathrm{rSPR}}$ equals the size of a maximum agreement forest minus one, and computing it is NP-hard, so is $d_{\mathrm{Head}}$. The reduction is polynomial because $\overline{T}$ has $2n^2+2$ leaves.

## Sources

- Remie Janssen, "Heading in the right direction? Using head moves to traverse phylogenetic network space", arXiv:1810.09795: Section 7, Definitions 18–22, Lemmas 32–34 and Theorem 6. <https://doi.org/10.48550/arXiv.1810.09795> Published version: Journal of Graph Algorithms and Applications 25 (2021) 263–310, <https://doi.org/10.7155/jgaa.00559>.
