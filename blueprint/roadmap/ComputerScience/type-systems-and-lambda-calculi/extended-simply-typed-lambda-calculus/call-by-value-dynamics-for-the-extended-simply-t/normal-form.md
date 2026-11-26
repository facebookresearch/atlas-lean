# Normal forms for call-by-value reduction

A term $t$ of type $A$ in a context $\Gamma$ is
in normal form when there is no term $t'$ such that $t$ reduces to $t'$ in one step.

This is `Relation.Normal Step` (see `normalForm_iff_normal`). Since `Step` never reduces under a
binder, every abstraction is a normal form here, even one whose body contains a redex.
