# RBAC$_{96}$ with dual role hierarchies enforces the liberal $*$-property

**Theorem.** An RBAC$_{96}$ system defined by [Construction 1](rbac96-configurations-for-a-security-lattice.md) satisfies the simple security property and the
liberal $*$-property of [lattice-based access control](lattice-based-access-control.md), with sessions as subjects: a session $s$ of a user cleared to $x$ has
$x \ge_{\mathrm{LBAC}} l(s)$, it can read an object $o$ only if $l(s) \ge_{\mathrm{LBAC}} l(o)$, and it can write $o$ only if $l(o) \ge_{\mathrm{LBAC}} l(s)$.

## Depends on

- [RBAC$_{96}$ configurations for a security lattice](rbac96-configurations-for-a-security-lattice.md)
- [Lattice-based access control](lattice-based-access-control.md)

## Sources

- S. Osborn, R. Sandhu and Q. Munawer, "Configuring role-based access control to enforce mandatory and discretionary access control policies", *ACM Transactions on Information and System Security* 3(2):85–106, 2000, <https://www.profsandhu.com/journals/tissec/dac00(org).pdf>: Section 4.2, Theorem 1 and its proof.
