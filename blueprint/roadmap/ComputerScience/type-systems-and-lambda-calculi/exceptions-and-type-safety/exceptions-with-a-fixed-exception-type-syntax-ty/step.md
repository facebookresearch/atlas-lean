# Small-step semantics of the calculus with exceptions

The rules are β-reduction of an
abstraction applied to a value, multiplication of numerals, the two zero-test rules, and:
* propagation (Wright and Felleisen's rule raise): an uncaught `raise v`, with `v` a value,
  leaves any admissible frame that is not a handler frame;
* `tryValue` (unhandle): `try v with x. e₂` steps to `v` for a value `v`;
* `tryRaise` (handle): `try (raise v) with x. e₂` steps to `e₂` with `x` instantiated by the
  value `v`;
* `frame`: steps are closed under admissible frames.
