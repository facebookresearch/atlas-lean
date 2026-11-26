# Linear dimension growth of graph-induced liftings

**Setting.** Let $\mathcal V=\{1,\dots,n\}$ be subpopulations with a nonnegative weight matrix $A=[a_{ij}]$ and effective transmission support $\mathcal E=\{(i,j):a_{ij}>0\}$ (diagonal pairs allowed), $m=|\mathcal E|$. With normalized fractions $S_i+E_i+I_i+R_i=1$, the networked SEIR model is
$$\dot S_i=-\beta\sum_j a_{ij}S_iI_j,\quad \dot E_i=\beta\sum_j a_{ij}S_iI_j-\sigma E_i,\quad \dot I_i=\sigma E_i-\gamma I_i,\quad \dot R_i=\gamma I_i,$$
with state $x\in\mathbb R^{4n}$ in the admissible set $\Omega$ (all compartments in $[0,1]$ summing to $1$ at each node, which is positively invariant). Write $\delta_i^{\mathrm{in}}=\sum_\ell a_{i\ell}$ for the weighted in-degree, $\delta^{\mathrm{in}}_{\max}=\max_i\delta_i^{\mathrm{in}}$, and $\Delta^{\mathrm{in}}$ for the maximum (unweighted) in-degree of the support.

Higher-order graph-induced dictionaries $\mathcal M_k$ of commutative degree-$k$ monomials are built recursively: $\mathcal M_2=\{S_iI_j, S_iE_j:(i,j)\in\mathcal E\}$ (so $|\mathcal M_2|=2m$), the quadratic transmission field applied to $\mathcal M_k$ generates new degree-$(k+1)$ monomials, and the linear compartmental field is then used to saturate them within degree $k+1$. The order-$d$ lifted state is $z_d=(x,\mathcal M_2,\dots,\mathcal M_d)$, whose dynamics are linear up to a residual containing only degree-$(d+1)$ terms.

**Statement.** Consider a family of transmission networks with $\Delta^{\mathrm{in}}\le\Delta$, where $\Delta\ge1$ does not depend on $n$. For every fixed $k\ge2$ there is a constant $C_k(\Delta)$, independent of $n$, with $|\mathcal M_k|\le C_k(\Delta)\,n$; one admissible choice is
$$C_2(\Delta)=2\Delta,\qquad C_{k+1}(\Delta)=2^{k+1}k\,\Delta\,C_k(\Delta)\quad(k\ge2).$$
Consequently, for fixed order $d$,
$$\dim z_d=4n+\sum_{k=2}^{d}|\mathcal M_k|=O(n),$$
whereas complete ordered or symmetric Kronecker liftings of the $4n$-dimensional state retain polynomial growth in $n$ whose degree increases with the order.

## Depends on

- [First edge-closure lifting of networked SEIR dynamics](first-edge-closure-lifting-of-networked-seir-dynamics.md)

## Expansion

For $k=2$, every channel belongs to exactly one receiving node's in-neighbourhood, so $m=\sum_i|\mathcal N^{\mathrm{in}}(i)|\le n\Delta$ and $|\mathcal M_2|=2m\le 2\Delta n$. For the induction step, take a degree-$k$ monomial. By the product rule the transmission field acts on one of its $k$ factors at a time, and a susceptible factor at node $i$ is coupled to at most $\Delta$ infectious factors through incoming channels, so each monomial generates a number of degree-$(k+1)$ monomials bounded in terms of $k$ and $\Delta$ only; linear saturation then changes compartment letters without changing node indices, contributing the factor $2^{k+1}$ in the recursion. Hence each fixed degree contributes $O(n)$ observables under bounded local connectivity, and sparse networks admit linear-size liftings at any fixed order.

## Sources

- Enrique Baeyens, "Graph-Induced Tensor Liftings for Networked SEIR Models: Dimensional Reduction and Residual Analysis", arXiv:2607.17664 (2026), Proposition 3, Proposition 4, Proposition 7 and Corollary 1, <https://doi.org/10.48550/arXiv.2607.17664>
