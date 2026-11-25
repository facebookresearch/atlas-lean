# Parabolic subgroups and the rational Bruhat decomposition of reductive groups

This node is still to be broken down. It covers the structure of parabolic subgroups of a connected
reductive group over a field, which the pages on automorphic forms, Eisenstein series, reduction theory
and $p$-adic groups use over number fields and local fields alike. Let $\mathbf{G}$ be a connected
reductive group over a field $k$.

- **Parabolic subgroups.** Parabolic $k$-subgroups $P$, $\mathbf{G}$ itself among them, and their Levi
  decompositions $P = M N$, with $N$ the unipotent radical, a $k$-split unipotent group, and $M$ a Levi
  $k$-subgroup; a minimal parabolic $k$-subgroup $P_0$ containing a maximal $k$-split torus $A_0$, which
  determines the set $\Delta_0$ of simple roots of the relative root system of $(\mathbf{G}, A_0)$; the standard
  parabolic subgroups, those containing $P_0$, which correspond to the subsets of $\Delta_0$ ($P_0$ to the empty
  set and $\mathbf{G}$ to $\Delta_0$), each with a unique Levi subgroup containing $A_0$; every parabolic $k$-subgroup
  is $\mathbf{G}(k)$-conjugate to exactly one standard parabolic subgroup, and every proper one is contained in a
  maximal proper parabolic $k$-subgroup ($\mathbf{G}$ itself lies in no proper one, and a torus has no proper
  parabolic subgroup); the relative Weyl group $W = N_{\mathbf{G}}(A_0)(k)/Z_{\mathbf{G}}(A_0)(k)$ and the Weyl groups $W_M$ of
  standard Levi subgroups.
- **Rational Bruhat decomposition.** For standard parabolic subgroups $P$ and $Q$ with standard Levi
  subgroups $M$ and $L$, $\mathbf{G}(k)$ is the disjoint union of the double cosets $P(k)\, w\, Q(k)$ for
  $w$ in a set of representatives of $W_M \backslash W / W_L$.
- **The general linear group.** For $\mathbf{G} = \mathrm{GL}_n$ the parabolic subgroups are the stabilizers
  of flags of subspaces of $k^n$; with $P_0$ the upper triangular group, the standard ones are the block
  upper triangular groups attached to the compositions $n = n_1 + \dots + n_r$, the maximal proper ones those of
  block sizes $(n_1, n_2)$, and $W$ is the symmetric group $S_n$.

## Expansion

A good expansion has definition pages for parabolic subgroups, Levi decompositions and standard
parabolic subgroups, statement pages for the conjugacy of parabolic subgroups to standard ones, for the
rational Bruhat decomposition and for the description of the parabolic subgroups of $\mathrm{GL}_n$, each
citing the sources below with locators; it serves both the local and the global pages, so that they need
not repeat it.

A good expansion also writes out these steps of its own proof:

- the Tits system of Borel and Tits, built from a minimal parabolic subgroup and the normalizer of a maximal split torus, from which the classification of the standard parabolic subgroups, the conjugacy of parabolic subgroups to standard ones and the rational Bruhat decomposition follow.

## Depends on

- [Linear algebraic groups over local fields and their groups of rational points](../../RepresentationTheory/reductive-groups-over-local-fields/linear-algebraic-groups-over-local-fields.md), for linear algebraic groups, connected reductive groups, split tori and unipotent radicals
- [Relative roots, root space decompositions and root subgroups of reductive groups](relative-root-systems-and-root-subgroups.md), for the relative root system of $(\mathbf{G}, A_0)$, its simple roots and the relative Weyl group

## Proof depends on

- [Relative roots, root space decompositions and root subgroups of reductive groups](relative-root-systems-and-root-subgroups.md), for the conjugacy of minimal parabolic subgroups and of maximal split tori, on which the Tits system rests

## Sources

- A. Borel and J. Tits, "Groupes réductifs", Publ. Math. IHÉS 27 (1965), 55–150,
  <http://www.numdam.org/item?id=PMIHES_1965__27__55_0>: §§4–5, in particular 5.12, p. 99 (the standard parabolic
  $k$-subgroups attached to the subsets of the simple $k$-roots, minimal for the empty set and equal to $G$ for
  all of them), 5.15, p. 100 (the Bruhat decomposition) and 5.20, p. 102 (the bijection
  $W_M \backslash W / W_L \cong P \backslash G / Q$), also cited by Bernstein and Zelevinsky (1977), §6.4.
- I. N. Bernstein and A. V. Zelevinsky, "Induced representations of reductive p-adic groups. I",
  Ann. Sci. École Norm. Sup. (4) 10 (1977), 441–472,
  <http://www.numdam.org/item?id=ASENS_1977_4_10_4_441_0>: §2.1 (minimal parabolic subgroups, maximal
  split tori, standard parabolic and Levi subgroups, Levi decompositions) and §6.4 (the Bruhat
  decomposition, "see [4], 5.15, 5.20").
