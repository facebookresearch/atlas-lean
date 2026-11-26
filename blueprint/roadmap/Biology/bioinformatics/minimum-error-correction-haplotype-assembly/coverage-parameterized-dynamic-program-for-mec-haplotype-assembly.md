# Coverage-parameterized dynamic program for minimum error correction haplotype assembly

**Setting.** Sequencing fragments from the two homologous copies of a chromosome are aligned to $n$
SNP sites and written as an $m \times n$ fragment matrix $M$ over $\{0, 1, -\}$, where $-$ means the site
is not observed in that fragment. Row $i$ **covers** column $j$ if it has a non-gap entry at $j$ or at
positions on both sides of $j$; the **coverage** of a column is the number of rows covering it, and
$t$ is the maximum coverage. In the **minimum error correction (MEC)** formulation, partition the rows
into two groups and choose haplotypes $h_1, h_2 \in \{0, 1\}^n$, one per group, to minimize the number of
non-gap entries that disagree with their group's haplotype (the number of entry flips needed to make
each group conflict-free).

**Recurrence.** Let $R_i$ be the rows covering column $i$, let $P$ range over the bipartitions of $R_i$, let
$C(P)$ be the number of minority entries in column $i$ summed over the two groups (the cost of setting
each group's haplotype to its majority value), and let $\mathrm{MEC}(i, P)$ be the optimal cost of the first
$i$ columns when column $i$ is split by $P$. For bipartitions $Q$ of $R_i \cap R_{i+1}$ set

$$\mathrm{ME}(i, Q) = \min_{P :\, P|_{R_i \cap R_{i+1}} = Q} \mathrm{MEC}(i, P), \qquad
\mathrm{MEC}(i + 1, P') = C(P') + \mathrm{ME}\bigl(i, P'|_{R_i \cap R_{i+1}}\bigr).$$

The optimum is $\min_{P} \mathrm{MEC}(n, P)$, recovered by backtracking.

**Theorem.** MEC haplotype assembly is solvable exactly in $O(n \cdot 2^{t} \cdot t)$ time, where $n$ is the
number of SNP columns and $t$ the maximum column coverage; in particular it is fixed-parameter
tractable in the coverage and linear in the number of sites.

## Expansion

Only rows covering a column can influence its correction cost, and the partition of the rows shared
by consecutive columns is all the information that must pass from one column to the next, because a
row's group is fixed once and for all. Each column has at most $2^t$ partitions of its covering rows,
restricting a partition and counting minorities take $O(t)$, and the table $\mathrm{ME}$ is filled by one
pass over the partitions of $R_i$. The haplotypes need not be complementary, unlike formulations that
assume heterozygosity at every site. With high coverage the exponent becomes prohibitive, so the
exact program is used on a subsample of fragments to seed a heuristic refinement.

## Sources

- F. Deng, W. Cui, L. Wang, "A highly accurate heuristic algorithm for the haplotype assembly
  problem", BMC Genomics 14(Suppl 2) (2013) S2, Methods, Eqs. 1-4 and Theorem 1,
  <https://doi.org/10.1186/1471-2164-14-s2-s2> (PMC3582451).
