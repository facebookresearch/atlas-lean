# Terminal currents of a conducting box as nodal injections

Let a conducting body occupy an axis-aligned box whose six faces are its terminals, and let $I_f$ be the outward current through
face $f$, the flux of the current density through that face. Suppose the enclosed charge $Q$ obeys the integrated continuity
equation $\sum_f I_f = -Q'(t)$. Attach each face $f$ to a node $\nu(f)$ of an arc network with node set $V$ and arc set $E$, and
let the device inject into node $v$ the current $j_v = \sum_{f : \nu(f) = v} I_f$ that leaves the box towards it. Let $B$ be the
head-positive incidence matrix, $B_{ve} = [h(e) = v] - [t(e) = v]$, so that $(B i)_v$ is the net arc current flowing into $v$ for
arc currents $i \in \mathbb R^E$; Kirchhoff's current law with the device attached reads $B i + j = 0$. Then

$$\sum_{v \in V} j_v = -Q'(t),$$

so arc currents satisfying Kirchhoff's current law can exist only if $Q'(t) = 0$: every column of $B$ sums to zero, hence
$\sum_v (B i)_v = 0$ for every $i$. When the enclosed charge is steady, the injections sum to zero and the box enters the network
as a six-terminal element whose terminal currents obey Kirchhoff's current law.

## Sources

- C. A. Desoer and E. S. Kuh, *Basic Circuit Theory*, McGraw-Hill, 1969 (Kirchhoff's current law and multiterminal elements).
- J. D. Jackson, *Classical Electrodynamics*, 3rd edition, Wiley, 1999 (the continuity equation for charge and current).
