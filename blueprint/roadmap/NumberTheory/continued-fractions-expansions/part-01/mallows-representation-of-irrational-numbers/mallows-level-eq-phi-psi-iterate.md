# Mallows levels from the Stern–Brocot maps

Encode each vertex of the Stern–Brocot tree
(left subtree, root $1/2$) by its gap, so that the root is the gap $(0/1, 1/1)$, and extend
$\psi_{\mathrm{SBT}}$ and $\varphi_{\mathrm{SBT}}$ to lists of vertices by applying them to each
entry and concatenating the results in order. Then for every $i \ge 1$ the ordered list $MT_i$
of fractions inserted at step $i$ of Mallows' construction is
$MT_i = \varphi_{\mathrm{SBT}}(\psi_{\mathrm{SBT}}^{\,i-1}(\langle 1/2\rangle))$, where
$\psi_{\mathrm{SBT}}^{\,i-1}$ is the $(i-1)$-fold iterate and $\langle 1/2\rangle$ is the list
whose only entry is the root.

The paper quotes this identity from Hida, J. Comb. 14 (2023).

## Sources

- Takanori Hida, *The Mallows Representation of the Irrational Numbers*, INTEGERS 25 (2025), Article A78, Theorem 1.
