# Two-counter session types

Two-counter session types describe infinite communication protocols by finitely many equations whose type constructors take two natural-number parameters. They sit above recursive, one-counter and pushdown session types and capture exactly the session types whose trace languages are decidable.

**Finite types (Gay, Poças and Vasconcelos).** Session types are built from the terminated type $\mathsf{end}$, input $?T.U$ (receive a value of type $T$, continue as $U$), output $!T.U$, external choice $\&\{\ell : T_\ell\}_{\ell \in L}$ (receive a label $k \in L$, continue as $T_k$) and internal choice $\oplus\{\ell : T_\ell\}_{\ell \in L}$ (select a label). Write $\sharp$ for $?$ or $!$ and $\star$ for $\&$ or $\oplus$.

**Equations with two counters.** Natural numbers are the terms $n ::= \mathsf{z} \mid \mathsf{s}\, n$. A system of *2-counter equations* fixes a finite set of type identifiers $X$, each applied to two natural numbers, and finitely many equations $X\langle p_1, p_2\rangle \doteq T$ in which each pattern $p_j$ is $\mathsf{z}$, $\mathsf{s}\, N_j$ or a variable $N_j$, the right-hand side $T$ is a type expression whose identifiers are applied to natural-number terms built from $\mathsf{z}$, $\mathsf{s}$, $N_1$ and $N_2$, and for each pair of numerals $(n_1, n_2)$ at most one equation of $X$ *matches* $X\langle n_1, n_2\rangle$ ($\mathsf{z}$ matches $\mathsf{z}$; $\mathsf{s}\, N_j$ matches $\mathsf{s}\, n$ with $N_j := n$; $N_j$ matches every $n$ with $N_j := n$). The matching equation *unfolds* $X\langle n_1, n_2\rangle$ to its right-hand side with these numerals substituted. This is the source's adaptation to two counters of its one-counter equations $X\langle \mathsf{z}\rangle \doteq T$, $X\langle \mathsf{s}\, N\rangle \doteq U$ (Figure 3), which the source leaves implicit; its example tests one counter per equation and leaves the other a variable. For example, $T_{\mathrm{iter}} = X\langle \mathsf{z}, \mathsf{z}\rangle$ under

$$
X\langle \mathsf{z}, N'\rangle \doteq\ ?\mathsf{end}.Y\langle \mathsf{z}, \mathsf{s}\,N'\rangle, \quad X\langle \mathsf{s}\,N, N'\rangle \doteq\ !\mathsf{end}.X\langle N, \mathsf{s}\,N'\rangle, \quad Y\langle N, \mathsf{z}\rangle \doteq X\langle N, \mathsf{z}\rangle, \quad Y\langle N, \mathsf{s}\,N'\rangle \doteq Y\langle \mathsf{s}\,N, N'\rangle
$$

unfolds to $?\mathsf{end}.\,!\mathsf{end}.\,?\mathsf{end}.\,!\mathsf{end}.\,!\mathsf{end}.\,?\mathsf{end} \cdots$, with $k$ outputs after the $k$-th input (Example 6).

**Judgements.** The rules below extend those of Figures 1–3 of the source, with one identifier rule for both counters in place of the one-counter rules C-z/C-s, T-z/T-s and E-zL/E-sL.

- *Contractiveness* ($T$ contr) is inductive: $\mathsf{end}$, every message type $\sharp T.U$ and every choice are contractive, and $X\langle n_1, n_2\rangle$ is contractive if it has a matching equation and its unfolding is contractive. So an identifier is contractive when finitely many unfoldings reach $\mathsf{end}$, a message or a choice.
- *Type formation* ($T\ \mathsf{type}_2$) is coinductive: $\mathsf{end}$ is a type; $\sharp T.U$ is a type if $T$ and $U$ are; a choice is a type if all its branches are; and $X\langle n_1, n_2\rangle$ is a type if it has a matching equation whose unfolding $U$ is contractive and a type.
- *Equivalence* ($T \simeq_2 U$) is coinductive: $\mathsf{end} \simeq_2 \mathsf{end}$; $\sharp T.V \simeq_2 \sharp U.W$ if $T \simeq_2 U$ and $V \simeq_2 W$ (same $\sharp$); $\star\{\ell : T_\ell\}_{\ell \in L} \simeq_2 \star\{\ell : U_\ell\}_{\ell \in L}$ if $T_\ell \simeq_2 U_\ell$ for all $\ell$ (same $\star$ and label set); and $X\langle n_1, n_2\rangle \simeq_2 T$ if its unfolding $U$ is contractive and $U \simeq_2 T$, and symmetrically on the right.
- *Duality* ($T \perp_2 U$) is coinductive: $\mathsf{end} \perp_2 \mathsf{end}$; $\sharp T.V \perp_2 \overline{\sharp} U.W$ if $T \simeq_2 U$ and $V \perp_2 W$, where $\overline{?} = {!}$ and $\overline{!} = {?}$; $\star\{\ell : T_\ell\}_{\ell \in L} \perp_2 \overline{\star}\{\ell : U_\ell\}_{\ell \in L}$ if $T_\ell \perp_2 U_\ell$ for all $\ell$, where $\overline{\&} = \oplus$ and $\overline{\oplus} = \&$; and identifiers on either side are unfolded as for equivalence.

Equivalently (Proposition 2 of the source), two types are equivalent iff they have the same infinite tree, or the same language of traces, and $T \perp_2 U$ iff $U$ is equivalent to the dual of $T$ obtained by swapping $?$ with $!$ and $\&$ with $\oplus$ along its continuations while keeping the types of the exchanged values (Lemma 8 and Theorem 12 of the source decide duality this way for the smaller classes).

A finite type, and every one-counter or pushdown session type, is a 2-counter type; $T_{\mathrm{iter}}$ is a 2-counter type that is not a pushdown type. By Theorem 5 of the source, an infinite session type is (the unfolding of) a 2-counter type exactly when its language of traces is decidable.

## Depends on

None.

## Proof depends on

None.

## Expansion

The hierarchy of the source is finite, recursive, one-counter, pushdown and 2-counter types, strictly increasing, with arbitrary coinductive infinite types at the top. Each class corresponds to an automaton model (finite-state, one-counter, pushdown, two-counter) accepting the traces of its types, which transfers decidability results from automata to types and back.

## Sources

- Simon J. Gay, Diogo Poças and Vasco T. Vasconcelos, "The Different Shades of Infinite Session Types", Foundations of Software Science and Computation Structures (FoSSaCS 2022), Lecture Notes in Computer Science 13242, pp. 347–367, Springer, 2022, <https://doi.org/10.1007/978-3-030-99253-8_18>. Read in arXiv:2201.08275v1, <https://arxiv.org/abs/2201.08275v1>; Section 2 (Figures 1–3 and the paragraph on the 2-counter world), Example 6, Theorem 2 (hierarchy), Lemma 4 and Theorem 5 (types and automata), numbering of arXiv:2201.08275v1.
