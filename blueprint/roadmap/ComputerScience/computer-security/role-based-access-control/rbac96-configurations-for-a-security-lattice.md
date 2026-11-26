# RBAC$_{96}$ configurations for a security lattice

Let $SC = \{L_1, \dots, L_n\}$ be a finite lattice of security labels, as in [lattice-based access control](lattice-based-access-control.md), with order $\ge_{\mathrm{LBAC}}$ and least element $L$. *Construction 1* configures an
[RBAC$_1$ system](rbac1-role-hierarchies.md) with constraints as follows:

- the roles are $R = \{L_1R, \dots, L_nR, L_1W, \dots, L_nW\}$, a read role and a write role for each label;
- $RH$ consists of two disjoint hierarchies: the read roles ordered as $\ge_{\mathrm{LBAC}}$ (so $xR \ge yR$ iff $x \ge_{\mathrm{LBAC}} y$), and the write roles ordered by the
  inverse of $\ge_{\mathrm{LBAC}}$;
- the permissions are $P = \{(o, r), (o, w) \mid o \text{ an object}\}$;
- each user is assigned by $UA$ to exactly the two roles $xR$ and $LW$, where $x$ is the user's clearance;
- each session has exactly two roles $yR$ and $yW$ for some label $y$, the label $l(s)$ of the session $s$;
- each object $o$ has a label $l(o) \in SC$, and the direct permission assignment $PA$ consists exactly of the pairs $((o, r), l(o)R)$ and $((o, w), l(o)W)$ for the
  objects $o$: each pair of permissions $(o, r), (o, w)$ is assigned to exactly one matching pair of roles $xR, xW$, respectively, and to no other role, so no write
  permission is assigned to a read role and no read permission to a write role. Inherited permissions are then determined by $RH$.

*Construction 2* is identical except that $RH$ orders the read roles as $\ge_{\mathrm{LBAC}}$ and relates no two distinct write roles. In both, a session $s$ can
read (write) $o$ when $(o, r)$ (respectively $(o, w)$) is among the permissions of its roles.

## Depends on

- [The RBAC$_1$ model: role hierarchies](rbac1-role-hierarchies.md)
- [Lattice-based access control](lattice-based-access-control.md)

## Sources

- S. Osborn, R. Sandhu and Q. Munawer, "Configuring role-based access control to enforce mandatory and discretionary access control policies", *ACM Transactions on Information and System Security* 3(2):85–106, 2000, <https://www.profsandhu.com/journals/tissec/dac00(org).pdf>: Section 4.1 (p. 93: each pair of permissions $(o, r), (o, w)$ assigned to exactly one matching pair of roles $xR, xW$, respectively), Section 4.2 (Construction 1) and Section 4.3 (Construction 2).
