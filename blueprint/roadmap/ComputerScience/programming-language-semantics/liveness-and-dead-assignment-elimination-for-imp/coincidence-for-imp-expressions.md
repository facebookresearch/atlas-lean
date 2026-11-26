# Coincidence for IMP expressions

Let $s_1$ and $s_2$ be [IMP states](../operational-semantics-of-imp/state.md).

1. If $s_1$ and $s_2$ agree on the variables of an [arithmetic expression](../operational-semantics-of-imp/aexp.md) $a$, then [$a$ evaluates](../operational-semantics-of-imp/eval.md) to the same value in $s_1$ and $s_2$.
2. If $s_1$ and $s_2$ agree on the variables of a [Boolean expression](../operational-semantics-of-imp/bexp.md) $b$, then [$b$ evaluates](../operational-semantics-of-imp/eval-2.md) to the same truth value in $s_1$ and $s_2$.

**Proof.** Induction on $a$ and on $b$.

## Depends on

- [IMP program states](../operational-semantics-of-imp/state.md)
- [Evaluation of IMP arithmetic expressions](../operational-semantics-of-imp/eval.md)
- [Evaluation of IMP Boolean expressions](../operational-semantics-of-imp/eval-2.md)
- [Arithmetic expressions of IMP](../operational-semantics-of-imp/aexp.md)
- [Boolean expressions of IMP](../operational-semantics-of-imp/bexp.md)

## Sources

- T. Nipkow and G. Klein, *Concrete Semantics with Isabelle/HOL*, Springer, 2014; revised version of January 21, 2026, <http://concrete-semantics.org/concrete-semantics.pdf>, Section 10.3.2, Lemma 10.17 (coincidence).
