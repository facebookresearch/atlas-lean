# Join-size estimation from shared-sign AMS sketches

Let $R$ be a relation over attributes $X \cup \{A\}$ and $S$ over $Y \cup \{A\}$ with $X$, $Y$ and $\{A\}$
pairwise disjoint, and let $f_i$, $g_i$ be the numbers of tuples of $R$ and $S$ with $A$-value $i$ (bag
semantics). Then $\lvert R \bowtie_A S \rvert = \sum_i f_i g_i$, and the self-join size of $R$ on $A$ (the
size of the join of $R$ with a copy of $R$ whose attributes other than $A$ are renamed apart) is
$F_2(f) = \sum_i f_i^2$. If $(s_i)$ is a family of signs that are pairwise independent and uniform on
$\{\pm 1\}$, shared by both sketches, then
$\mathbb{E}\bigl[(\sum_i s_i f_i)(\sum_i s_i g_i)\bigr] = \sum_i f_i g_i$, so the product of the two sketches is
an unbiased estimator of the join size. Unbiasedness uses pairwise independence only. For the self-join
case $g = f$ with four-wise independent signs, the
[unbiasedness of the AMS second-moment sketch](integral-sketch-sq.md),
its [variance bound](variance-sketch-sq-le.md)
and the [median-of-means estimate](measure-real-ams-estimate-le.md)
are stated on their own pages.

The identity $\mathbb{E}[s_i s_j] = 0$ for $i \ne j$ is the only property of the signs the proof uses.

## Depends on

- [Bag relations and bag relational algebra](../../databases/bags-and-nulls/bag-relations-and-bag-relational-algebra.md)

## Sources

- Tracking Join and Self-Join Sizes in Limited Storage (Alon, Gibbons, Matias, Szegedy), J. Comput. System Sci. 64(3) 2002, author copy, Section 4.3, Lemma 4.4(1) and its proof (stated for four-wise independent signs; the proof uses only $\mathbb{E}[s_i s_j] = 0$ for $i \ne j$). <http://theory.stanford.edu/~matias/papers/tracking_jcss.pdf>
- The Space Complexity of Approximating the Frequency Moments (Alon, Matias, Szegedy) — JCSS 58 (1999) / STOC 1996, Theorem 2.2 and its proof (the second-moment sketch). <https://web.math.princeton.edu/~nalon/PDFS/amsz4.pdf>
