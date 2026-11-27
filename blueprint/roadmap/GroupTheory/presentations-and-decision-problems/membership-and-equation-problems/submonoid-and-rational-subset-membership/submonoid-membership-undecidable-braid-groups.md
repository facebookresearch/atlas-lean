# Submonoid membership is undecidable in the braid groups B_n for n at least 4

The braid group $B_n$ has decidable submonoid membership problem exactly when $n \leq 3$; for $n \geq 4$ it contains a fixed finitely generated submonoid with undecidable membership, and in $B_4$ the fixed-target submonoid membership and subsemigroup intersection problems are undecidable too.

For $n \geq 2$ let $B_n$ be the braid group on $n$ strands, with generators $\sigma_1, \dots, \sigma_{n-1}$ and relations $\sigma_i \sigma_j = \sigma_j \sigma_i$ for $|i - j| \geq 2$ and $\sigma_i \sigma_{i+1} \sigma_i = \sigma_{i+1} \sigma_i \sigma_{i+1}$. For a finite set $X$ of elements of a group, $\mathrm{Mon}(X)$ and $\mathrm{Sgp}(X)$ denote the submonoid and the subsemigroup it generates. The [submonoid membership problem](submonoid-membership-problem.md) asks, given a finite set $X$ and an element $g$, whether $g \in \mathrm{Mon}(X)$; for a fixed element $\gamma$, the *fixed-target submonoid membership problem for $\gamma$* asks, given a finite set $X$, whether $\gamma \in \mathrm{Mon}(X)$; the *subsemigroup intersection problem* asks, given finite sets $X$ and $Y$, whether $\mathrm{Sgp}(X) \cap \mathrm{Sgp}(Y) = \varnothing$. Elements are given as words in the generators and their inverses.

**Theorem (Gray and Nyberg-Brodda).**

1. $B_n$ has decidable submonoid membership problem if and only if $n \leq 3$. For $n \leq 3$, $B_n$ even has decidable [rational subset membership problem](rational-subset-membership-problem.md); for $n \geq 4$, $B_n$ contains a fixed finitely generated submonoid $\mathrm{Mon}(X)$ in which membership is undecidable (Theorem 3.1 of arXiv:2409.11335v3).
2. In [$B_4$](../../braid-and-artin/braid-groups-in-automorphism-groups-of-free-grou/braid-group-four.md), with $\gamma_0 = \sigma_2^2 \sigma_1^2 \sigma_2^{-2} \sigma_1^{-2}$: the fixed-target submonoid membership problem for $\gamma_0$ is undecidable, and no algorithm decides, given a finite set $X \subseteq B_4$, whether $\mathrm{Sgp}(X) \cap \mathrm{Sgp}(\gamma_0) = \varnothing$; in particular the subsemigroup intersection problem of $B_4$ is undecidable (Theorem 3.7 of arXiv:2409.11335v3).

This answers Potapov's question whether submonoid membership is decidable in $B_4$. The subgroup membership problem of $B_n$ is undecidable for $n \geq 5$ (Makanina); $B_4$ does not contain $F_2 \times F_2$ (by a result of Akimenkov, as the source recalls), and the source leaves open whether its subgroup membership problem is decidable. The source extends the classification to all Artin groups (Theorem 4.4); an independent characterization of the Artin groups with undecidable submonoid membership is on the page [An Artin group has undecidable submonoid membership exactly when it contains A(P4) or A(C4)](artin-groups-submonoid-membership-characterization.md).

## Depends on

- [Submonoid membership problem](submonoid-membership-problem.md)
- [Rational subset membership problem](rational-subset-membership-problem.md)
- [The braid group B4](../../braid-and-artin/braid-groups-in-automorphism-groups-of-free-grou/braid-group-four.md)
- [Group](../../../group-basics/group.md)
- [Braid group on n strands](../../braid-and-artin/endomorphisms-of-braid-groups/braid-group.md)

## Proof depends on

None.

## Expansion

By a theorem of Droms, Lewin and Servatius, the elements $\sigma_2^2$, $(\sigma_2 \sigma_3 \sigma_2)^2$, $\sigma_3^2$ and $\sigma_1^2$ of $B_4$ generate a copy of the right-angled Artin group $A(P_4)$ of the path on four vertices, so $A(P_4)$ embeds in $B_n$ for every $n \geq 4$. Lohrey and Steinberg proved that $A(P_4)$ contains a fixed finitely generated submonoid with undecidable membership, and a fixed submonoid of a subgroup stays one of the whole group. For $n \leq 3$, $B_3$ has a finite-index subgroup isomorphic to $F_k \times \mathbb{Z}$, whose rational subset membership problem is decidable (Kambites), and decidability of rational subset membership passes to finite-index overgroups. Part 2 is proved in $A(P_4)$ by encoding the undecidable fixed-target and intersection problems there, then transferring them along the embedding. A complete expansion links pages for the Lohrey–Steinberg theorem on $A(P_4)$ and for the Droms–Lewin–Servatius embedding, neither of which has a page.

## Sources

- R. D. Gray and C.-F. Nyberg-Brodda, "Membership problems in braid groups and Artin groups", *Journal of the London Mathematical Society* 112(4), 2025, article e70326, doi:10.1112/jlms.70326; read as arXiv:2409.11335v3, <https://arxiv.org/abs/2409.11335v3>: Theorems 3.1, 3.3 (Droms, Lewin and Servatius), 3.7 and 4.4 and the introduction, with the numbering of that version.
- M. Lohrey and B. Steinberg, "The submonoid and rational subset membership problems for graph groups", *Journal of Algebra* 320(2):728–755, 2008, doi:10.1016/j.jalgebra.2007.08.025 (cited beside the copy read, which states its theorem as Theorem 3.2).
