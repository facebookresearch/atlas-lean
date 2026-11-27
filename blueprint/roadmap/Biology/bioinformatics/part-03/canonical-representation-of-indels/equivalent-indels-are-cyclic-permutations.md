# Equivalent indels are cyclic permutations

Let $R$ be a reference sequence. An **insertion** of a nonempty string $d$ at position $p$ produces $R[1..p]\,d\,R[p+1..]$; a **deletion** of $d = R[p+1..p+|d|]$ produces $R[1..p]\,R[p+|d|+1..]$. Two indels of the same type and length are **equivalent** if they produce the same alternate sequence. In repetitive context one variant can be written at many positions, which causes discordant calls between tools and databases.

**Theorem.** All indels equivalent to a given one lie within a single contiguous **region of equivalence**, and their indel strings are cyclic permutations (conjugates) of one another: if $d_1$ placed at the left of the region and $d_2$ placed at the right are equivalent, then $d_1 = uv$ and $d_2 = vu$ for some strings $u, v$, and every intermediate placement spells a rotation of $d_1$.

**UPS coordinate.** Starting from a reported indel, extending the region of equivalence as far as possible to the left and right (while the shifted indel remains equivalent) yields a canonical interval, the **Universal Positioning System coordinate**; two indel calls describe the same variant if and only if they have the same type, the same UPS interval and the same indel string when placed at the left end of that interval (the UPS coordinate records this pattern with the interval), so the comparison is independent of the left- or right-alignment convention used by a caller.

## Depends on

- [Rotation orbit of a tuple](../../../../Combinatorics/elementary-enumeration/necklaces-over-a-group-with-identity-product/tuple-rotation-orbit.md)

## Expansion

If $d_1$ and $d_2$ are inserted at the two ends of a stretch $S$ of the reference and give the same result, then $d_1 S = S d_2$. By the Lyndon–Schützenberger theorem on the equation $xz = zy$ in a free monoid, $d_1 = uv$, $d_2 = vu$ and $S = (uv)^j u$ for some $j \ge 0$; so $S$ is periodic with period $|d_1|$ and sliding the insertion one position at a time through $S$ rotates the inserted string by one character. Deletions are handled the same way, with the deleted string read from the reference. This is why calls made by different pipelines on repeats can be compared only after moving them to a common end of the region of equivalence.

## Sources

- M. S. Hasan, X. Wu, L. T. Watson and L. Zhang, "UPS-indel: a Universal Positioning System for Indels", Scientific Reports 7 (2017), Theorem 1 and the UPS-indel algorithm, <https://doi.org/10.1038/s41598-017-14400-1>, PMCID: PMC5658412.
- R. C. Lyndon and M.-P. Schützenberger, "The equation $a^M = b^N c^P$ in a free group", Michigan Mathematical Journal 9 (1962), 289–298, <https://doi.org/10.1307/mmj/1028998766>.
