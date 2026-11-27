# Characterization sets of minimal finite-state machines

A deterministic, completely specified Mealy machine $M$ has a finite state set $Q$, an input alphabet $I$, an output
alphabet $O$, an initial state, a transition function $\delta : Q \times I \to Q$ and an output function $\lambda : Q \times I \to O$,
extended to words so that $\lambda^*(q, w)$ is the output word produced from state $q$ on input word $w$. States $q$ and $q'$ are
*equivalent* if $\lambda^*(q, w) = \lambda^*(q', w)$ for every input word $w$, and $M$ is *minimal* if equivalent states are equal. A
*characterization set* of $M$ is a finite set $W$ of input words containing the empty word such that any two states $q$, $q'$
with $\lambda^*(q, w) = \lambda^*(q', w)$ for all $w \in W$ are equivalent.

**Theorem.** If $M$ is minimal with $n \ge 1$ states, it has a characterization set all of whose words have length at most
$n - 1$. For $n = 1$ the set $\{\varepsilon\}$ suffices.

Proof: call $q$ and $q'$ $k$-equivalent if they agree on all input words of length at most $k$. $0$-equivalence has one
class, $(k+1)$-equivalence refines $k$-equivalence, and if $(k+1)$-equivalence equals $k$-equivalence then every larger level
is also equal. Each strict refinement adds a class, and there are at most $n$ classes, so $(n-1)$-equivalence is
equivalence. Choosing, for each pair of distinct states, one input word of length at most $n - 1$ on which they differ,
together with $\varepsilon$, gives $W$.

## Sources

- B. Kocsis and J. Rot, "Complete test suites for automata in monoidal closed categories", arXiv:2411.13412v2: Definitions 2.1 and 2.3 (equivalence, minimality, characterization set containing the empty word) and Section 5.1 (Mealy machines). The length bound and its proof are derived on this page.
- T. S. Chow, "Testing software design modeled by finite-state machines", *IEEE Transactions on Software Engineering* SE-4(3):178–187, 1978.
