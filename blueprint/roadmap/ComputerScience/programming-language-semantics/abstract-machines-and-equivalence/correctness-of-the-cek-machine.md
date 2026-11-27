# Correctness of the CEK machine

For closed terms of the call-by-value lambda calculus (and in particular closed well-typed simply typed terms), the CEK machine with states consisting of a control term, an environment of closures and a continuation, started on the term with the empty environment and the empty continuation, reaches a final state with a value closure $\langle \lambda x.e, \rho\rangle$ if and only if the term evaluates by big-step call-by-value semantics to the value obtained by substituting the environment $\rho$ into $\lambda x.e$. For well-typed terms the machine never gets stuck.

## Depends on

- [Typed de Bruijn variables of the simply typed lambda calculus](../../type-systems-and-lambda-calculi/simply-typed-lambda-calculus/var.md)

## Expansion

This page becomes ready once:

- CEK machine states and transition rules, and the substitution interpretation of closures and environments as terms (statement prerequisite; not yet stated)
- Big-step call-by-value semantics of the untyped λ-calculus (statement prerequisite; not yet stated)

## Sources

- M. Felleisen and D. P. Friedman, "Control operators, the SECD-machine, and the lambda-calculus", *Formal Description of Programming Concepts III*, North-Holland, 1986
- M. Felleisen, R. B. Findler and M. Flatt, *Semantics Engineering with PLT Redex*, MIT Press, 2009
