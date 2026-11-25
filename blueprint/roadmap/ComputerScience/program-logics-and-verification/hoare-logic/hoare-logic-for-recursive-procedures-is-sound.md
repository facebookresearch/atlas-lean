# Hoare logic for recursive procedures is sound and relatively complete

Use the language with one parameterless recursive procedure, its big-step semantics, assertions with auxiliary state,
validity and the proof system of [soundness of the recursion rule](soundness-of-the-recursion-rule.md). Its consequence rule
is: from $C \vdash \{P'\}\,c\,\{Q'\}$ infer $C \vdash \{P\}\,c\,\{Q\}$ provided that for all states $s$ and $t$, if $P'(z', s)$ implies $Q'(z', t)$ for all
$z'$, then $P(z, s)$ implies $Q(z, t)$ for all $z$. This rule handles adaptation to auxiliary variables, so no separate invariance or
substitution rules are needed. Then:

- every triple derivable in the empty context is valid (soundness);
- every valid triple $\{P\}\,c\,\{Q\}$ whose assertions have auxiliary state of the same type as program states is derivable in the
  empty context (completeness for semantic assertions).

Completeness uses the most general triple $\mathrm{MGT}(c) = (\lambda z\, s.\ z = s,\ c,\ \lambda z\, t.\ z \xrightarrow{c} t)$: if $C \vdash \mathrm{MGT}(\mathbf{call})$
then $C \vdash \mathrm{MGT}(c)$ for every $c$, so the assumption and recursion rules give $\emptyset \vdash \mathrm{MGT}(c)$, from which every valid triple
follows by the consequence rule. The result holds for unbounded nondeterminism.

## Depends on

- [Soundness of the recursion rule](soundness-of-the-recursion-rule.md)

## Proof depends on

- [Soundness of the recursion rule](soundness-of-the-recursion-rule.md)

## Sources

- T. Nipkow, "Hoare logics for recursive procedures and unbounded nondeterminism", *Computer Science Logic (CSL 2002)*, LNCS 2471, Springer, 2002, <https://www21.in.tum.de/~nipkow/pubs/csl02.pdf>: Section 3 (consequence rule, soundness theorem, most general triple, MGT-lemma and completeness theorem).
- C. A. R. Hoare, "Procedures and parameters: an axiomatic approach", *Symposium on Semantics of Algorithmic Languages*, LNM 188, Springer, 1971.
- K. R. Apt, F. S. de Boer and E.-R. Olderog, *Verification of Sequential and Concurrent Programs*, 3rd ed., Springer, 2009.
