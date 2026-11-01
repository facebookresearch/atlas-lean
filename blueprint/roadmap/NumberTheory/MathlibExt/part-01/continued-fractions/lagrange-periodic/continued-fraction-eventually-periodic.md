---
article_id: af_afc1c31f44744554ca959826
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.ContinuedFractionEventuallyPeriodic
---

# Continued Fraction Eventually Periodic

Eventual periodicity of the continued fraction of `x`: the expansion does not
terminate, and the tail partial denominators `partDens` (which omits the head
coefficient `a₀`) are eventually periodic. Nontermination rules out a
vacuous `Option.none` tail. Source: Nimbran–Levrie lines 130–134.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Is Eventually Periodic](../../../../../Dynamics/MathlibExt/eventually-periodic-sequence/is-eventually-periodic.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.ContinuedFractions.LagrangePeriodic](../../../../../../sources/v2/MathlibExt.md)
