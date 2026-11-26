# Conditional entropy of segmentations via their union

**Setting.** A segmentation $P$ of a sequence of length $N$ (for example a genomic region split into coding/non-coding stretches or isochores) is a partition of the positions $\{1,\dots,N\}$ into $k_P$ contiguous segments $\bar p_1,\dots,\bar p_{k_P}$, given by boundaries $0=p_0<p_1<\dots<p_{k_P}=N$. Choosing a position uniformly at random makes each segment an event with $\Pr(\bar p_i)=|\bar p_i|/N$. The entropy of $P$ is

$$H(P)=-\sum_{i=1}^{k_P}\Pr(\bar p_i)\log\Pr(\bar p_i)\le \log N ,$$

and for a second segmentation $Q$ the conditional entropy of $P$ given $Q$ is

$$H(P\mid Q)=-\sum_{j=1}^{k_Q}\sum_{i=1}^{k_P}\Pr(\bar p_i,\bar q_j)\log\Pr(\bar p_i\mid \bar q_j),$$

the expected information needed to identify the segment of $P$ containing a random position once its segment of $Q$ is known.

**Lemma (union formula).** Let $U=P\cup Q$ be the segmentation whose boundaries are all boundaries of $P$ or of $Q$. Then

$$H(P\mid Q)=H(U)-H(Q).$$

Consequently $H(P\mid Q)$ and $H(Q\mid P)$ can be computed in $O(k_P+k_Q)$ time by merging the two sorted boundary lists.

**Asymmetry.** If $Q$ has a single segment then $H(P\mid Q)=H(P)$ while $H(Q\mid P)=0$; if $Q$ has $N$ singleton segments then $H(P\mid Q)=0$ while $H(Q\mid P)=\log N-H(P)$. Hence two segmentations should be called similar only when both conditional entropies are small; the entropy distance $D_H(P,Q)=H(P\mid Q)+H(Q\mid P)=2H(U)-H(P)-H(Q)$ alone can be small for segmentations that differ substantially.

## Expansion

The non-empty intersections $\bar p_i\cap\bar q_j$ are exactly the segments of $U$, so $-\sum_{i,j}\Pr(\bar p_i,\bar q_j)\log\Pr(\bar p_i,\bar q_j)=H(U)$. Writing $\log\Pr(\bar p_i\mid\bar q_j)=\log\Pr(\bar p_i,\bar q_j)-\log\Pr(\bar q_j)$ and summing over $i$ first gives $H(U)+\sum_j\Pr(\bar q_j)\log\Pr(\bar q_j)=H(U)-H(Q)$. The two extreme examples follow directly from the union formula, since in the first case $U=P$ and in the second $U=Q$.

## Sources

- N. Haiminen, H. Mannila, E. Terzi, "Comparing segmentations by applying randomization techniques", BMC Bioinformatics 8:171 (2007), Methods (definitions of segmentation entropy and conditional entropy, Lemma 1, and the discussion of the entropy distance), <https://doi.org/10.1186/1471-2105-8-171>, PMCID: PMC1904250.
