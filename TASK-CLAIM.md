# Task claim: isomorphism of affine virtual dihedral quandles

This temporary note opens the draft pull request that claims the ATLAS task
`af_eda169a16feb6f77a117b0fe`. It will be removed when the proof lands on this branch.

- Article: `blueprint/roadmap/Algebra/nonassociative-algebras/virtual-racks-and-quandles/dihedral-virtual-rack-iso-iff.md`
- Lean declaration: `MetaMathlibExt.dihedral_virtualRackIso_iff`, a `theorem_wanted` in
  `WantedExt/Algebra/VirtualQuandleWanted.lean`
- Source: Lực Ta, *Enumeration of Virtual Quandles Up to Isomorphism*, Journal of Integer
  Sequences 28 (2025), Article 25.8.4, Proposition 21.

Statement to prove, with its name and statement unchanged: let $n > 0$, let $R_n$ be the dihedral
quandle on $\mathbb{Z}/n\mathbb{Z}$ (with $x \triangleleft y = 2x - y$), and for
$a \in \mathbb{Z}/n\mathbb{Z}$ and $u \in (\mathbb{Z}/n\mathbb{Z})^\times$ let $T_{a,u}$ be the
permutation $x \mapsto a + u x$ of $R_n$. For all $a, b \in \mathbb{Z}/n\mathbb{Z}$ and
$u, v \in (\mathbb{Z}/n\mathbb{Z})^\times$, the virtual racks $(R_n, T_{a,u})$ and
$(R_n, T_{b,v})$ are isomorphic if and only if $u = v$ and $b = y a + (1 - u) x$ for some
$x \in \mathbb{Z}/n\mathbb{Z}$ and $y \in (\mathbb{Z}/n\mathbb{Z})^\times$.
