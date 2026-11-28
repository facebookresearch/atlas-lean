# Heap-language commands are safety monotone, termination monotone and framing

In the RAM model with nondeterministic allocation, every command of the heap language with assignment, lookup, mutation, allocation, disposal, sequencing, conditionals and while loops is safety monotone and termination monotone and has the frame property.

Consider the heap language whose stores map variables to integers and whose heaps are finite partial maps from natural-number addresses to integers, with commands $x := E$, $x := [E]$, $[E] := F$, $x := \mathrm{cons}(E_1, \dots, E_n)$, $\mathrm{dispose}(E)$, $C ; C'$, $\mathbf{if}\ B\ \mathbf{then}\ C\ \mathbf{else}\ C'$ and $\mathbf{while}\ B\ \mathbf{do}\ C$. Lookup, mutation and disposal fault at an unallocated address, and $\mathrm{cons}$ picks any $n$ consecutive addresses not in use. For every command $C$, store $s$ and heaps $h, h', h_0, h_1$:

1. if $C, s, h$ is safe and $h \# h'$, then $C, s, h \ast h'$ is safe;
2. if $C, s, h$ must terminate normally and $h \# h'$, then $C, s, h \ast h'$ must terminate normally;
3. if $C, s, h_0$ is safe and $C, s, h_0 \ast h_1 \leadsto^\ast s', h'$, then $C, s, h_0 \leadsto^\ast s', h_0'$ for some $h_0'$ with $h' = h_0' \ast h_1$;

that is, every command has the three properties of [safety monotonicity and the frame property](safety-monotonicity-and-the-frame-property.md) in operational form.

## Depends on

- [Safety monotonicity and the frame property](safety-monotonicity-and-the-frame-property.md)

## Proof depends on

- [Safety monotonicity and the frame property](safety-monotonicity-and-the-frame-property.md)

## Expansion

Missing prerequisite of a proof page: the small-step operational semantics of this heap language, with configurations, the fault configuration and nondeterministic allocation, has no page. The proof is by induction on the derivation of executions, stated simultaneously for terminal and non-terminal configurations. For allocation, an address segment fresh for $h_0 \ast h_1$ is also fresh for $h_0$; for mutation, lookup and disposal, safety on $h_0$ places the accessed address in $h_0$ and hence outside $h_1$; sequencing, conditionals and loops follow from the induction hypothesis. The source relies on nondeterministic allocation in an essential way: if the smallest free address were always chosen, adding memory would change the newly allocated address, the difference could be detected with address arithmetic, and the frame rule would be invalidated.

## Sources

- H. Yang and P. O'Hearn, "A semantic basis for local reasoning", *Foundations of Software Science and Computation Structures (FoSSaCS 2002)*, LNCS 2303, Springer, 2002, pp. 402–416, <https://doi.org/10.1007/3-540-45931-6_28>, author copy <http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/basis.pdf>, Section 2 (the language, stores, heaps and operational semantics), Section 4, Lemma 1 (safety and termination monotonicity), Lemma 2 (frame property) and its proof, and Section 4.1 (nondeterministic allocation).
