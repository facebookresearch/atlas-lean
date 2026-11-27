# Two-counter session types

Two-counter session types describe infinite communication protocols by finitely many equations whose type constructors take two natural-number parameters. They sit above recursive, one-counter and pushdown session types and capture exactly the session types whose trace languages are decidable.

**Finite types (Gay, Poças and Vasconcelos).** Session types are built from the terminated type $\mathsf{end}$, input $?T.U$ (receive a value of type $T$, continue as $U$), output $!T.U$, external choice $\&\{\ell : T_\ell\}_{\ell \in L}$ (receive a label $k \in L$, continue as $T_k$) and internal choice $\oplus\{\ell : T_\ell\}_{\ell \in L}$ (select a label). Write $\sharp$ for $?$ or $!$ and $\star$ for $\&$ or $\oplus$.

**Equations with two counters.** Natural numbers are the terms $n ::= \mathsf{z} \mid \mathsf{s}\, n$. A system of *2-counter equations* fixes a finite set of type constructors $X$, each applied to two natural-number arguments, and finitely many equations $X\langle p, p'\rangle \doteq T$ whose left-hand sides distinguish $\mathsf{z}$ from $\mathsf{s}\,N$ in the arguments, with natural-number variables $N, N'$; a right-hand side $T$ may mention those variables, and $T[n/N, n'/N']$ is $T$ with numerals substituted. The rules are the adaptation of the one-counter rules, where each $X$ has at most one equation $X\langle \mathsf{z}\rangle \doteq T$ and one $X\langle \mathsf{s}\,N\rangle \doteq U$. For example, $T_{\mathrm{iter}} = X\langle \mathsf{z}, \mathsf{z}\rangle$ under

$$
X\langle \mathsf{z}, N'\rangle \doteq\ ?\mathsf{end}.Y\langle \mathsf{z}, \mathsf{s}\,N'\rangle, \quad X\langle \mathsf{s}\,N, N'\rangle \doteq\ !\mathsf{end}.X\langle N, \mathsf{s}\,N'\rangle, \quad Y\langle N, \mathsf{z}\rangle \doteq X\langle N, \mathsf{z}\rangle, \quad Y\langle N, \mathsf{s}\,N'\rangle \doteq Y\langle \mathsf{s}\,N, N'\rangle
$$

unfolds to $?\mathsf{end}.\,!\mathsf{end}.\,?\mathsf{end}.\,!\mathsf{end}.\,!\mathsf{end}.\,?\mathsf{end} \cdots$, with $k$ outputs after the $k$-th input.

**Judgements.** A type identifier $X\langle n, n'\rangle$ is *contractive* if finitely many unfoldings of its equations reach a type constructor ($\mathsf{end}$, a message or a choice) rather than another identifier; contractiveness is inductive. Type formation $T\ \mathsf{type}_2$ (for an identifier: the right-hand side of its equation, instantiated, is contractive and is itself a type), type equivalence $T \simeq_2 U$ and duality $T \perp_2 U$ are interpreted coinductively. Duality swaps $?$ with $!$ and $\&$ with $\oplus$ and requires exchanged types to be equivalent.

A finite type, and every one-counter or pushdown session type, is a 2-counter type; $T_{\mathrm{iter}}$ is a 2-counter type that is not a pushdown type. By Theorem 5 of the source, an infinite session type is (the unfolding of) a 2-counter type exactly when its language of traces is decidable.

## Depends on

None.

## Proof depends on

None.

## Expansion

The hierarchy of the source is finite, recursive, one-counter, pushdown and 2-counter types, strictly increasing, with arbitrary coinductive infinite types at the top. Each class corresponds to an automaton model (finite-state, one-counter, pushdown, two-counter) accepting the traces of its types, which transfers decidability results from automata to types and back.

## Sources

- Simon J. Gay, Diogo Poças and Vasco T. Vasconcelos, "The Different Shades of Infinite Session Types", Foundations of Software Science and Computation Structures (FoSSaCS 2022), Lecture Notes in Computer Science 13242, pp. 347–367, Springer, 2022, <https://doi.org/10.1007/978-3-030-99253-8_18>. Read in arXiv:2201.08275v1, <https://arxiv.org/abs/2201.08275v1>; Section 2 (Figures 1–3 and the paragraph on the 2-counter world), Example 6, Theorem 2 (hierarchy), Lemma 4 and Theorem 5 (types and automata), numbering of arXiv:2201.08275v1.
