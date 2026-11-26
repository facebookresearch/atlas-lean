# Free-model handlers: exceptions, state run laws, explicit nondeterminism

## Signatures and free models

- [Signature of exceptions](except-f.md)
- [Free model of exceptions](free-except.md)
- [Signature of explicit nondeterminism](nondet-f.md)
- [Raw failure-and-choice trees](free-nondet.md)

## Exceptions

- [Raising an exception](raise.md)
- [Exception handler](handle.md)
- [Handling a pure return](handle-pure.md)
- [Handling a raised exception](handle-raise-bind.md)
- [Uniqueness of the exception handler](handle-unique.md)
- [Running an exception computation](run.md)
- [Running a pure return](run-pure.md)
- [Running a raise](run-raise.md)
- [A first error short-circuits a bind](run-bind-error.md)

## State

- [Reading the state twice](run-get-get.md)
- [Reading and writing back the state](run-get-set.md)
- [Running get then set](run-get-set-pure.md)
- [Reading right after writing](run-set-get.md)
- [Running set then get](run-set-get-pure.md)
- [Two writes in a row](run-set-set.md)
- [Running set then set](run-set-set-pure.md)

## Explicit nondeterminism

- [Failure](fail.md)
- [Binary choice](choice.md)

## Sources

- G. Plotkin and M. Pretnar, *Handlers of Algebraic Effects*, Programming Languages and Systems (ESOP 2009): Section 2 (exceptions) and Section 6.4 (explicit nondeterminism, `fail : 0` and `pick : 2`). In the later journal version, explicit nondeterminism is Section 3.1.
