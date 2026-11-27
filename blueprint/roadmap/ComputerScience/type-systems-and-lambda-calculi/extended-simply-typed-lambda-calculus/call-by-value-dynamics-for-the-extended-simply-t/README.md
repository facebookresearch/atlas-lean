# Call-by-value dynamics for the extended simply typed lambda calculus

## Stlc Extended

- [Values of the extended simply typed lambda calculus](value.md)
- [Small-step call-by-value reduction in the extended calculus](step.md)

## Value

- [A variable is not a value](not-var.md)
- [An application is not a value](not-app.md)
- [A first projection is not a value](not-fst.md)
- [A second projection is not a value](not-snd.md)
- [A case analysis is not a value](not-case.md)
- [A conditional is not a value](not-ite.md)
- [A `let` is not a value](not-let-in.md)

## Stlc Extended

- [Canonical forms at function types](closed-value-arr.md)
- [Canonical forms at product types](closed-value-prod.md)
- [Canonical forms at sum types](closed-value-sum.md)
- [Canonical forms at the boolean type](closed-value-bool.md)
- [Canonical forms at the unit type](closed-value-unit.md)

## Step

- [Values are irreducible](value-irreducible.md)
- [Progress for closed terms](progress.md)
- [Call-by-value reduction is deterministic](deterministic.md)
- [Normal forms for call-by-value reduction](normal-form.md)
- [Normal forms are the normal forms of the step relation](normal-form-iff-normal.md)
- [Closed normal forms are exactly the values](closed-normal-form-iff-value.md)

## Stlc Extended

- [Multi-step call-by-value reduction](steps.md)

## Steps

- [A term reduces to at most one value](value-unique.md)
- [Multi-step reduction in the function of an application](app-fun.md)
- [Multi-step reduction in the argument of an application whose function is a value](app-arg.md)
- [Multi-step reduction in the left component of a pair](pair-l.md)
- [Multi-step reduction in the right component of a pair whose left component is a value](pair-r.md)
- [Multi-step reduction in the argument of a first projection](fst.md)
- [Multi-step reduction in the argument of a second projection](snd.md)
- [Multi-step reduction in the payload of a left injection](inl.md)
- [Multi-step reduction in the payload of a right injection](inr.md)
- [Multi-step reduction in the scrutinee of a case analysis](case.md)
- [Multi-step reduction in the condition of a conditional](ite.md)
- [Multi-step reduction in the bound term of a `let`](let-l.md)
