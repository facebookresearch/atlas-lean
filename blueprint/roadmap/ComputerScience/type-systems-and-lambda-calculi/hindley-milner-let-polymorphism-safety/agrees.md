# Agreement of δ with the signature

The hypotheses on a δ-relation, for the signature
$K$:

- every δ-redex is a destructor applied to exactly as many values as its arity;
- the δ-reduct of a well-formed δ-redex is well formed;
- δ-reduction of a well-formed δ-redex preserves types in the initial context (Pottier and
  Rémy, Definition 10.5.5 (i));
- a well-formed constant application to values that is well typed in the initial context is a
  value or reduces (Definition 10.5.5 (ii)). The reduction need not be a δ-step at the root: a
  destructor applied to more values than its arity reduces in the evaluation context of the
  application, by reducing its saturated head.

The last three conditions concern only well-formed expressions, which bind no constant: the
source keeps program variables and constants apart (§10.1), so an expression that binds a
constant name is no program and places no obligation on δ.
