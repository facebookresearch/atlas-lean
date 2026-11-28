# Counting tree-child and normal networks with one reticulation

**Notation.** Let $a_{n,k}$ be the number of tree-child networks and $b_{n,k}$ the number of normal networks with $k$ reticulations on $[1,n]$ ($0\le k<n$, and $a_{n,k}=b_{n,k}=0$ for $k\ge n$). For a tree-child network $N$ let $u(N)$ be the number of unordered pairs of incomparable edges of $N$, and let $u_{n,k}=\sum_{N\in\mathrm{TCN}_k(n)}u(N)$.

**Theorem (recurrences).** For $n\ge3$,

$$a_{n,k}=(2n+k-3)\bigl\{a_{n-1,k}+(2n+k-4)\,a_{n-1,k-1}\bigr\}+u_{n-1,k-1},$$

with $a_{2,0}=1$ and $a_{2,1}=2$, and

$$b_{n,n-1}=0,\qquad b_{n,1}=(2n-2)\,b_{n-1,1}+3\,u_{n-1,0}\quad(n>2),$$

where $u_{n-1,0}$ is the total number of unordered incomparable edge pairs over all rooted binary phylogenetic trees on $n-1$ taxa.

**Lemma (incomparable edge pairs in trees).** For $n\ge2$,

$$u_{n,0}=\frac{(n+1)\,(2n)!}{2^n\,n!}-2^n\,n!,$$

and the total number of comparable pairs over all trees on $n$ taxa is $c_n=2^n n!-\dfrac{(2n)!}{2^{n-1}n!}$.

**Theorem (one reticulation).** For $n\ge3$,

$$a_{n,1}=\frac{(2n)!}{2^n\,(n-1)!}-2^{n-1}\,n!,\qquad b_{n,1}=\frac{(n+2)\,(2n)!}{2^n\,n!}-3\cdot2^{n-1}\,n!.$$

Every rooted binary network with exactly one reticulation is tree-child, so $a_{n,1}$ also counts all rooted binary phylogenetic networks with one reticulation. For example $a_{3,1}=21$, $a_{4,1}=228$, $b_{3,1}=3$, $b_{4,1}=54$ and $b_{5,1}=855$.

## Depends on

- [Unique generation of tree-child and normal networks by leaf and reticulation insertion](unique-generation-of-tree-child-networks-by-leaf-and-reticulation-insertion.md)

## Expansion

A network in $\mathrm{TCN}_k(n-1)$ has $2n+k-3$ tree edges, which gives the leaf-insertion term. A network in $\mathrm{TCN}_{k-1}(n-1)$ has $2n+k-4$ tree edges, so a reticulation can be inserted in $(2n+k-4)+\binom{2n+k-4}{2}$ ways. Each single edge and each comparable pair yields two networks (insertion with or without one rotation), and each incomparable pair yields three. This gives $(2n+k-3)(2n+k-4)a_{n-1,k-1}+u_{n-1,k-1}$. For normal networks only incomparable pairs are usable, and in a tree all three outcomes are normal. The tree lemma follows from tracking how a leaf insertion changes the number of ordered comparable pairs, which gives $c_n=2n\,c_{n-1}+2(2n-2)!/(2^{n-1}(n-1)!)$, summed with Catalan-number identities. Substituting into the recurrences and summing the resulting series gives the closed forms. For $k\ge2$ the exact counts (Table 1, up to $n=8$) come from enumeration, and no simple closed formula is known.

## Sources

- L. Zhang, "Generating normal networks via leaf insertion and nearest neighbor interchange", *BMC Bioinformatics* 20 (Suppl 20):642 (2019), Theorem 3 (Eqs. 1–3), Lemma 1 (Eq. 4), Theorem 4 (Eqs. 6–7), Remark 1, Table 1, <https://doi.org/10.1186/s12859-019-3209-3>, PMCID PMC6915859.
