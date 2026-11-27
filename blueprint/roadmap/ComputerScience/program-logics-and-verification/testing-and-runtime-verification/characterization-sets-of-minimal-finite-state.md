# Characterization sets of finite-state machines

A deterministic, completely specified Mealy machine $M$ has a finite state set $Q$, an input alphabet $I$ and an output
alphabet $O$ (neither need be finite), an initial state, a transition function $\delta : Q \times I \to Q$ and an output
function $\lambda : Q \times I \to O$, extended to words so that $\lambda^*(q, w)$ is the output word produced from state
$q$ on input word $w$. States $q$ and $q'$ are *equivalent* if $\lambda^*(q, w) = \lambda^*(q', w)$ for every input word
$w$. A *characterization set* of $M$ is a finite set $W$ of input words containing the empty word $\varepsilon$ such that
any two states $q$, $q'$ with $\lambda^*(q, w) = \lambda^*(q', w)$ for all $w \in W$ are equivalent.

**Theorem.** If $M$ has $n$ states (so $n \ge 1$, as $M$ has an initial state), it has a characterization set all of
whose words have length at most $n - 1$.

## Remarks

$M$ is *minimal* if equivalent states are equal; in a minimal machine, a characterization set separates any two distinct
states. The theorem does not need minimality. For $n = 1$ the bound leaves only the set $\{\varepsilon\}$.

Since $\lambda^*(q, \varepsilon) = \varepsilon$ for every state, the empty word separates no states. The bound $n - 1$
cannot be lowered: in the machine with one input letter $a$, states $q_0, q_1, q_2$, transitions
$q_0 \to q_1 \to q_2 \to q_2$, and output $1$ on the transition out of $q_2$ and $0$ on the others, the states $q_0$ and
$q_1$ agree on every input word of length at most $1$, while $\lambda^*(q_0, aa) = 00$ and $\lambda^*(q_1, aa) = 01$; so
every characterization set of this machine contains a word of length at least $2 = n - 1$.

## Proof

Call $q$ and $q'$ *$k$-equivalent* if they agree on all input words of length at most $k$. $0$-equivalence has one
class, since $\lambda^*(q, \varepsilon) = \varepsilon$ for every $q$. States $q$ and $q'$ are $(k+1)$-equivalent exactly
when $\lambda(q, a) = \lambda(q', a)$ and $\delta(q, a)$ and $\delta(q', a)$ are $k$-equivalent for every input $a$. So
$(k+1)$-equivalence refines $k$-equivalence, and if $(k+1)$-equivalence equals $k$-equivalence then
$(k+2)$-equivalence equals $(k+1)$-equivalence; then every larger level is also equal, and $k$-equivalence is
equivalence. Each strict refinement adds a class, and there are at most $n$ classes, so $(n-1)$-equivalence is
equivalence. Choosing, for each pair of inequivalent states, one input word of length at most $n - 1$ on which their
output words differ, together with $\varepsilon$, gives $W$.

## Sources

- B. Kocsis and J. Rot, "Complete test suites for automata in monoidal closed categories", arXiv:2411.13412v2: Definitions 2.1 and 2.3 (equivalence, minimality, characterization set containing the empty word, stated for DFAs) and Section 5.1 (Mealy machines, and the extension $\lambda^*$ of the output function that records every output of a run). The length bound and its proof are derived on this page.
- T. S. Chow, "Testing software design modeled by finite-state machines", *IEEE Transactions on Software Engineering* SE-4(3):178–187, 1978.
