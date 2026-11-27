# The endomorphism double twisted conjugacy problem is undecidable in free groups of rank at least 32

For a free group $F_n$ of rank $n \ge 32$, no algorithm decides, given endomorphisms $\phi, \psi$ of $F_n$ and elements $u, v$, whether $u\, w^\phi = w^\psi\, v$ for some $w \in F_n$; yet the twisted conjugacy problem of $F_n$ is decidable.

The double twisted conjugacy problem for endomorphisms is undecidable in $F_n$ for $n \ge 32$. Here, for endomorphisms $\phi, \psi$ of a group $G$, elements $u, v \in G$ are $(\phi, \psi)$-double-twisted conjugate if there is $w \in G$ with $u\, w^\phi = w^\psi\, v$, where $w^\phi$ denotes the image of $w$ under $\phi$. The endomorphism double twisted conjugacy problem asks for an algorithm that decides this, given $\phi$ and $\psi$ (by the images of the generators) and $u, v$ (as words).

1. For a free group $F_n$ of rank $n \ge 32$, the endomorphism double twisted conjugacy problem is undecidable (corollary in Section 4 of the source).
2. Free groups of rank at least 32 therefore have decidable twisted conjugacy problem (Bogopolski, Martino, Maslakova and Ventura) and undecidable endomorphism double twisted conjugacy problem, answering a question of Ventura.
3. For the free solvable group $S_{m,n}$ of class $m \ge 3$ and rank $n$ at least a constant $N_{\mathrm{sol}}$ (the least total number of generators and relators of a finite presentation of a solvable group with undecidable word problem), the endomorphism double twisted conjugacy problem is undecidable.

## Depends on

- [Group](../../../group-basics/group.md)
- [Multiplication-preserving maps and group homomorphisms](../../../semigroups-and-monoids/group-homomorphism.md)
- [Twisted conjugacy problem](twisted-conjugacy-problem.md)
- [Solvable word problem](../../word-problem-for-groups/word-problem-solvable.md)

## Proof depends on

- [The generalized Post correspondence problem is undecidable in every group containing a non-abelian free subgroup](../../membership-and-equation-problems/post-correspondence-problem-for-groups/gpcp-undecidable-groups-with-free-subgroups.md)

## Expansion

In a relatively free group with basis $a_1, \dots, a_n$, an instance of $\mathrm{GPCP}_n$ with pairs $(g_i, h_i)$ and constant $a$ is the same as asking whether $a$ and $1$ are double twisted conjugate for the endomorphisms sending $a_i \mapsto g_i$ and $a_i \mapsto h_i$; so the endomorphism double twisted conjugacy problem is linear-time equivalent to $\mathrm{GPCP}_n(G)$ (a proposition in Section 3 of the source). Undecidability of $\mathrm{GPCP}_n(F_n)$ for $n \ge 32$ then gives the result; for free solvable groups the source uses Kharlampovich's finitely presented solvable group with undecidable word problem.

## Sources

- A. Myasnikov, A. Nikolaev and A. Ushakov, "The Post correspondence problem in groups", Journal of Group Theory 17 (2014), no. 6, 991–1008, https://doi.org/10.1515/jgth-2014-0022; read in arXiv:1310.5246v2 (the proposition relating $\mathrm{GPCP}$ and double twisted conjugacy in Section 3, and the corollaries in Section 4, of arXiv:1310.5246v2).
