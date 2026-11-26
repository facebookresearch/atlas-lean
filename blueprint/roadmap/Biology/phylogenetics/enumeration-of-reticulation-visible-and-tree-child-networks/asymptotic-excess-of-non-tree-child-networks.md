# Asymptotic excess of non-tree-child networks

**Setting.** Let $\mathcal P_{\ell,k}$ be the set of all binary phylogenetic networks with $\ell$ labeled leaves and $k$ reticulations (root of out-degree $1$, tree nodes of in/out-degree $1/2$, reticulations of in/out-degree $2/1$), and let $TC_{\ell,k}\subseteq RV_{\ell,k}\subseteq \mathcal P_{\ell,k}$ be the tree-child and reticulation-visible networks, with $\Delta_k(\ell)=|RV_{\ell,k}|-|TC_{\ell,k}|$. A *violation* is a non-leaf vertex all of whose children are reticulations (a reticulation whose child is a reticulation, or a tree node with two reticulation children); a network is tree-child if and only if it has no violation.

**Statement.** For every fixed $k\ge 2$, as $\ell\to\infty$,
$$|\mathcal P_{\ell,k}|-TC_{\ell,k} = 4(k-1)\,\ell\,TC_{\ell,k-1}\bigl(1+O(\ell^{-1/2})\bigr),\qquad \Delta_k(\ell) = 2(k-1)\,\ell\,TC_{\ell,k-1}\bigl(1+O(\ell^{-1/2})\bigr),$$
and consequently
$$\frac{|\mathcal P_{\ell,k}|-TC_{\ell,k}}{TC_{\ell,k}}\sim\frac{2k(k-1)}{\ell},\qquad \frac{\Delta_k(\ell)}{TC_{\ell,k}}\sim\frac{k(k-1)}{\ell} .$$
In particular all three counts share the leading asymptotics $TC_{\ell,k}\sim RV_{\ell,k}\sim \frac{2^{k-1}\sqrt2}{k!}\left(\frac{2}{e}\right)^{\ell}\ell^{\ell+2k-1}$. If, moreover, $\Delta_k(\ell)=A_k(\ell)(2\ell-3)!!-B_k(\ell)2^{\ell-k+1}\ell!$ for polynomials $A_k,B_k$ and all large $\ell$, then $\deg A_k=2k-1$, the leading coefficient of $A_k$ is $2^k/(k-2)!$, and $\deg B_k\le 2k-3$.

## Depends on

- [Exact difference between reticulation-visible and tree-child network counts](exact-difference-between-reticulation-visible-and-tree-child-counts.md)

## Expansion

Split non-tree-child networks by their violations. Networks with at least two violations are $O(TC_{\ell,k-1})$, since removing one reticulation edge leaves a structure from a set of size $O(\ell^{-1}TC_{\ell,k-1})$ and the edge can be reinserted in $O(\ell)$ ways, or the removal also destroys the second violation, which pins both insertion points to $O(1)$ edges near reticulations. A network with a single violation is obtained from a tree-child network with $k-1$ reticulations by inserting one reticulation edge so as to create exactly one stack or one tree node with two reticulation children; with $2\ell+O(1)$ edges available the two kinds each contribute $2(k-1)\ell\,TC_{\ell,k-1}$ to leading order (a tree-node violation is produced twice, once from each removal, which the count corrects for). A network with a stack $r\to r'$ is never reticulation-visible: a root path to the second parent of $r'$, continued through $r'$, reaches every leaf below $r$ while avoiding $r$. In contrast, all but $O(TC_{\ell,k-1})$ networks whose single violation is a tree node are reticulation-visible, since from each reticulation one can walk down through tree nodes avoiding the violation to a leaf. Hence only the tree-node half contributes to $\Delta_k$. The ratio statements use $TC_{\ell,k}/TC_{\ell,k-1}\sim 2\ell^2/k$ from the leading asymptotics. For the polynomial form, $(2\ell-3)!!/(2^{\ell}\ell!)$ decays like $\ell^{-3/2}$ (a half-integer power) while the $B_k$ term gives an integer power, so they cannot cancel and matching $\Delta_k/(2^\ell\ell!)\sim \frac{2^k}{(k-2)!}\frac{\ell^{2k-5/2}}{2\sqrt\pi}$ fixes the degree and leading coefficient of $A_k$. The case $k=2$ recovers the leading coefficient $4$ of $4\ell^3+3\ell^2-\ell-1$.

## Sources

- Josep Batle, "Exact Enumeration of Phylogenetic Networks: The Tree-Child, Reticulation-Visible and Orchard Hierarchy", arXiv:2606.24325 (2026), Theorem 3.5, Theorem 5.7, Corollary 5.9 and Corollary 5.10, <https://doi.org/10.48550/arXiv.2606.24325>
