# Full flat split systems and the four-point condition

**Setting.** Flat split systems are as in the companion article; all splits are proper (both parts nonempty). For $Y\subseteq X$ the *induced* split system is

$$ \mathcal S_{|Y}=\{(A\cap Y)\,|\,(B\cap Y) : A|B\in\mathcal S,\ A\cap Y\ne\emptyset,\ B\cap Y\ne\emptyset\} . $$

A flat split system on $n=|X|$ elements is *full* if it has $\binom n2$ splits.

**Theorem.**

1. Every flat split system on $X$ is contained in a flat split system on $X$ with exactly $\binom n2$ splits; this is the maximum size of a flat split system.
2. A split system $\mathcal S$ on $X$ with $|\mathcal S|=\binom n2$ is flat (hence full) if and only if, for every $Y\subseteq X$ with $|Y|=4$, the induced system $\mathcal S_{|Y}$ contains exactly $6$ splits.
3. Consequently every flat split system satisfies $|\mathcal S_{|Y}|\le 6$ for all four-element $Y$; a system with some $|\mathcal S_{|Y}|=7$ has no planar split network representation.

## Depends on

- [Planar split networks represent exactly the flat split systems](planar-split-networks-represent-exactly-the-flat-split-systems.md)

## Expansion

A flat system of size $s$ corresponds to an oriented matroid with $2s+2$ topes. A rank-$3$ uniform oriented matroid on $n$ elements has $2\binom{n-1}{2}+2\binom{n-1}{1}+2$ topes, which gives $s=\binom n2$; a smaller flat system comes from a non-uniform matroid in which three pseudolines are concurrent, and perturbing one of them adds topes without losing any, until the matroid is uniform. For the four-point criterion, deletion of all but four elements of a uniform rank-$3$ matroid leaves a uniform one with $14$ topes, that is $6$ splits; conversely the condition bounds the VC dimension of the tope set by $3$, and a characterization of uniform oriented matroids by VC dimension then shows the splits come from a uniform rank-$3$ oriented matroid.

## Sources

- M. Balvočiūtė, D. Bryant and A. Spillner, *When can splits be drawn in the plane?*, arXiv:1509.06104 (2015). <https://doi.org/10.48550/arXiv.1509.06104> Section 4 (Maximal split systems): extension theorem, four-point theorem and the remark following it. The paper's results are unnumbered. Published version: SIAM Journal on Discrete Mathematics 31 (2017) 839–856, <https://doi.org/10.1137/15m1040852>.
