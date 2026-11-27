# The identity and group problems for semigroups of braids on five strands are undecidable

No algorithm decides, given finitely many braids on five strands, whether some nonempty composition of them is isotopic to the trivial braid, or whether the semigroup they generate is a group.

Let $B_n$ be the braid group on $n$ strands, with generators $\sigma_1, \dots, \sigma_{n-1}$; composition of braids is the group operation, and two braids are equal in $B_n$ exactly when they are isotopic. For a finite set $\{b_1, \dots, b_k\} \subseteq B_n$, let $\langle b_1, \dots, b_k \rangle$ be the semigroup it generates. The *identity problem* asks whether the trivial braid lies in $\langle b_1, \dots, b_k \rangle$, that is, whether some nonempty composition of the given braids is isotopic to the trivial braid. The *group problem* asks whether $\langle b_1, \dots, b_k \rangle$ is a group, that is, whether the inverse of each $b_i$ is a composition of braids from the set.

**Theorem (Potapov).** The identity problem and the group problem are undecidable for braids in $B_5$ (Theorem 14 of the copy read).

The braids, given as words in the generators, are the input; the number of strands is fixed at $5$. For $B_3$ the membership problem for semigroups of braids is NP-hard and decidable (Theorems 11 and 12 of the same paper), so the identity problem and the group problem, which ask about membership of the trivial braid and of the inverses of the generators, are decidable there as well; the case of $B_4$ is left open in the paper. Later, Gray and Nyberg-Brodda showed that $B_4$ has undecidable submonoid membership, fixed-target submonoid membership and subsemigroup intersection problems ([submonoid membership is undecidable in the braid groups](submonoid-membership-undecidable-braid-groups.md)); they record the identity problem in $B_4$ as still open.

## Depends on

- [Group](../../../group-basics/group.md)
- [Braid group on n strands](../../braid-and-artin/endomorphisms-of-braid-groups/braid-group.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The subgroups $\langle \sigma_1^4, \sigma_2^4 \rangle$ and $\langle \sigma_4^2, d \rangle$ of $B_5$, with $d = \sigma_4 \sigma_3 \sigma_2 \sigma_1^2 \sigma_2 \sigma_3 \sigma_4$, are free of rank $2$ and generate their direct product inside $B_5$ (Lemma 13, quoted from the literature). The proof reduces the Identity Correspondence Problem of Bell and Potapov: given pairs $(s_i, t_i)$ of elements of the free group on $\{a, b\}$, is there a nonempty sequence of indices with $s_{l_1} \cdots s_{l_k} = t_{l_1} \cdots t_{l_k} = 1$? Each pair $(s, t)$ is sent to the braid $\varphi(s)\psi(t)$, where $\varphi(a) = \sigma_1^4$, $\varphi(b) = \sigma_2^4$, $\psi(a) = \sigma_4^2$, $\psi(b) = d$; since these maps are injective homomorphisms into commuting free factors, the trivial braid is a composition of the resulting braids exactly when the instance has a solution, and the group problem is handled with the same encoding. A good expansion links the undecidability of the Identity Correspondence Problem and the embedding of $F_2 \times F_2$ into $B_5$, which have no pages on main.

## Sources

- I. Potapov, "Composition problems for braids", in *IARCS Annual Conference on Foundations of Software Technology and Theoretical Computer Science (FSTTCS 2013)*, Leibniz International Proceedings in Informatics 24, 2013, pp. 175–187, doi:10.4230/LIPIcs.FSTTCS.2013.175; read in the open-access copy at <https://drops.dagstuhl.de/storage/00lipics/lipics-vol024-fsttcs2013/LIPIcs.FSTTCS.2013.175/LIPIcs.FSTTCS.2013.175.pdf>: the problem definitions of Section 1, Theorems 11, 12 and 14 and Lemma 13 with the proof of Theorem 14, in the numbering of that copy.
- S.-K. Ko and I. Potapov, "Composition problems for braids: membership, identity and freeness", arXiv:1707.08389v1, <https://arxiv.org/abs/1707.08389v1>: an extended version restating the theorem, cited beside the refereed paper above.
