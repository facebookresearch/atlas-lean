# Total-correctness frame rule for the heap language

For the heap language with integer values and nondeterministic allocation, the frame rule with the side condition that the frame is independent of the variables the command modifies is sound for total correctness: termination monotonicity carries must-termination from the small heap to the framed one.

For a set $X$ of variables let $\forall X.\, p = \{(s, h) : (s[s_X], h) \in p \text{ for all } s_X : X \to \mathbb{Z}\}$, and let $X \# p$ mean $p = \forall X.\, p$; let $\mathrm{Modifies}(C)$ be the set of variables assigned in $C$. Call $\{p\}\, C\, \{q\}$ true for total correctness if from every $(s, h) \in p$ the configuration $C, s, h$ must terminate normally, that is, it is safe and has no infinite execution, and every terminal state reached satisfies $q$. Then for every command $C$ of the heap language of [heap-language commands are safety monotone, termination monotone and framing](heap-language-commands-satisfy-locality.md) and all predicates $p, q, r$ with $\mathrm{Modifies}(C) \# r$, if $\{p\}\, C\, \{q\}$ is true for total correctness, so is $\{p \ast r\}\, C\, \{q \ast r\}$.

## Depends on

- [Heap-language commands are safety monotone, termination monotone and framing](heap-language-commands-satisfy-locality.md)
- [Safety monotonicity and the frame property](safety-monotonicity-and-the-frame-property.md)

## Proof depends on

- [Heap-language commands are safety monotone, termination monotone and framing](heap-language-commands-satisfy-locality.md)

## Expansion

Missing prerequisites of a proof page: the operational semantics of this heap language (shared with the page above) and the locality of variables, that an execution leaves unchanged every variable not assigned in the command. Given $s, h_0 \models p$ and $s, h_1 \models r$, termination monotonicity makes $C, s, h_0 \ast h_1$ terminate normally; for a terminal $s', h$ the frame property gives $h = h_0' \ast h_1$ with $s', h_0' \models q$, and since $s'$ agrees with $s$ outside $\mathrm{Modifies}(C)$ and $r$ is independent of those variables, $s', h_1 \models r$. The same source proves the fault-avoiding partial-correctness version, using safety monotonicity instead of termination monotonicity. That partial-correctness frame rule, for a heap language with natural-number heap values, is the page [frame rule](../../separation-logic/frame.md); this page differs from it in its total-correctness reading and in the language, which has integer values and nondeterministic allocation. The abstract, variable-free counterpart, an equivalence, is [frame rule soundness is equivalent to safety monotonicity and the frame property](frame-rule-soundness-and-operational-locality.md).

## Sources

- H. Yang and P. O'Hearn, "A semantic basis for local reasoning", *Foundations of Software Science and Computation Structures (FoSSaCS 2002)*, LNCS 2303, Springer, 2002, pp. 402–416, <https://doi.org/10.1007/3-540-45931-6_28>, author copy <http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/basis.pdf>, Section 3 (total correctness, $\forall X.\, p$, $X \# p$ and the semantic frame rule) and Section 4, Theorem 1 and the total-correctness sentence of its proof.
