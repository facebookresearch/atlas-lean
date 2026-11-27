# Lattice-based access control

In *lattice-based access control* (LBAC) each subject $s$ and each object $o$ has a security label $l(s)$, $l(o)$ drawn from a finite lattice $SC$ of security labels
with a partially ordered dominance relation $\ge$ and a least upper bound operator, and labels do not change (tranquillity). A user is cleared to a label and
may run subjects at any label dominated by the clearance. The mandatory rules are:

- *simple security property:* $s$ can read $o$ only if $l(s) \ge l(o)$;
- *liberal $*$-property:* $s$ can write $o$ only if $l(s) \le l(o)$;
- *strict $*$-property:* $s$ can write $o$ only if $l(s) = l(o)$.

Information therefore flows only upward in the lattice; the lattice of labels is that of
[security levels](../information-flow/security-levels-policies-and-low-equivalence.md).

## Depends on

- [Security levels, policies and low equivalence](../information-flow/security-levels-policies-and-low-equivalence.md)

## Sources

- S. Osborn, R. Sandhu and Q. Munawer, "Configuring role-based access control to enforce mandatory and discretionary access control policies", *ACM Transactions on Information and System Security* 3(2):85–106, 2000, <https://www.profsandhu.com/journals/tissec/dac00(org).pdf>: Section 3, Definitions 2–5.
