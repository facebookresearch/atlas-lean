# RBAC$_{96}$ with unordered write roles enforces the strict $*$-property

**Theorem.** An RBAC$_{96}$ system defined by [Construction 2](rbac96-configurations-for-a-security-lattice.md) satisfies the simple security property and the
strict $*$-property of [lattice-based access control](lattice-based-access-control.md), with sessions as subjects: a session $s$ can read an object $o$ only if
$l(s) \ge_{\mathrm{LBAC}} l(o)$, and it can write $o$ only if $l(o) = l(s)$.

## Depends on

- [RBAC$_{96}$ configurations for a security lattice](rbac96-configurations-for-a-security-lattice.md)
- [Lattice-based access control](lattice-based-access-control.md)

## Sources

- S. Osborn, R. Sandhu and Q. Munawer, "Configuring role-based access control to enforce mandatory and discretionary access control policies", *ACM Transactions on Information and System Security* 3(2):85–106, 2000, <https://www.profsandhu.com/journals/tissec/dac00(org).pdf>: Section 4.3, Theorem 2 (its proof is omitted there as analogous to that of Theorem 1).
