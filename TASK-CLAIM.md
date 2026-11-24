# Task claim: index of the Jacobi symbol kernel

This temporary note opens the draft pull request that claims the ATLAS task
`af_67ed67cd3b5da93997c35fd8`. It will be removed when the proof lands on this branch.

- Article: `blueprint/roadmap/Combinatorics/additive-combinatorics/zero-sum-subset-sums/weighted-davenport-constant/part-04/jacobi-kernel-index-two.md`
- Lean declaration: `MetaMathlibExt.jacobi_kernel_index_two`, a `theorem_wanted` in
  `WantedExt/NumberTheory/JacobiZeroSumConstantsWanted.lean`
- Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *Zero-Sum Constants Related to the
  Jacobi Symbol*, Journal of Integer Sequences 27 (2024), Article 24.1.7, Proposition 11.

Statement to prove, with its name and statement unchanged: let $n$ be odd and
$S(n) = \{u \in U(n) : (u/n) = 1\}$ in the unit group $U(n)$ of $\mathbb{Z}/n\mathbb{Z}$. If $n$ is
not a perfect square, $S(n)$ is a subgroup of $U(n)$ of index $2$; if $n$ is a perfect square,
$S(n) = U(n)$.
