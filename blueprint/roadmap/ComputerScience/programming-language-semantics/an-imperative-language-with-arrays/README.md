# An imperative language with arrays

A variant of IMP with variables named by strings, natural-number arithmetic with truncated
subtraction and division, reads from immutable arrays and while loops annotated with invariants,
with its big-step semantics. The language without arrays is the topic
[Operational semantics of IMP](../operational-semantics-of-imp/README.md).

- [Fuel-bounded interpreter for the imperative language with arrays](exec.md)
- [Soundness of the interpreter for the imperative language with arrays](exec-sound.md)
- [An out-of-bounds array read has no execution](read-no-big-step.md)
- [The interpreter fails on an out-of-bounds array read](exec-read-invalid.md)
- [Evaluation of arithmetic expressions in the imperative language with arrays](eval-a.md)
- [Truth of Boolean expressions in the imperative language with arrays](beval.md)
- [Updating a state of the imperative language with arrays](update.md)
- [Big-step semantics of the imperative language with arrays](big-step.md)
- [Arithmetic expressions of the imperative language with arrays](aexp.md)
- [Boolean expressions of the imperative language with arrays](bexp.md)
- [States of the imperative language with arrays](state.md)
- [Statements of the imperative language with arrays](stmt.md)
- [The increment statement as an example](incr-x.md)
