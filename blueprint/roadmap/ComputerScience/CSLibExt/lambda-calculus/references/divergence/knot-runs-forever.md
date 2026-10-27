---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Languages.LambdaCalculus.References.knot_runs_forever
---

# Knot runs forever

Nor does it get stuck: every configuration reachable from the knot takes a
further step, so its evaluation runs forever.

## Depends on

- [Knot](knot.md)
- [Step](../semantics/step.md)
- [Steps](../semantics/steps.md)
- [Store](../semantics/store.md)
- [Term](../syntax/term.md)

## Proof depends on

- [Body](body.md)
- [Body₀](body-2.md)
- [C₁](c.md)
- [Id U](id-u.md)
- [Loop A](loop-a.md)
- [Reachable](reachable.md)
- [Deterministic](../semantics/deterministic.md)
- [Value](../syntax/value.md)
- [Instantiate](../syntax/instantiate.md)
- [Ty](../syntax/ty.md)

## Sources

- [CSLibExt, CSLibExt.Languages.LambdaCalculus.References.Divergence](../../../../../../sources/v2/CSLibExt.md)
