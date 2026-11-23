# Multiresolution approximation of $L^2(\mathbb{R})$

A sequence $(V_j)_{j \in \mathbb{Z}}$ of closed subspaces of $L^2(\mathbb{R})$ is a multiresolution approximation (S. Mallat, *Multiresolution approximations and wavelet orthonormal bases of $L^2(\mathbb{R})$*, Trans. Amer. Math. Soc. 315 (1989), Definition, properties (1)–(5)) if
1. $V_j \subset V_{j+1}$ for every $j$;
2. $\bigcup_j V_j$ is dense in $L^2(\mathbb{R})$ and $\bigcap_j V_j = \{0\}$;
3. $f(x) \in V_j \iff f(2x) \in V_{j+1}$;
4. $f(x) \in V_j \implies f(x - 2^{-j}k) \in V_j$ for every $k \in \mathbb{Z}$;
5. there is an isomorphism $I : V_0 \to \ell^2(\mathbb{Z})$ which commutes with the action of $\mathbb{Z}$, by integer translation on $V_0$ and by shift on $\ell^2(\mathbb{Z})$.

The orthogonal projection on $V_j$ is the approximation of $f$ at resolution $2^j$. Here the subspaces are complex linear subspaces of $L^2(\mathbb{R})$, a dilated or translated function means any element of $L^2(\mathbb{R})$ almost everywhere equal to it, and the isomorphism in (5) is a bounded linear isomorphism with bounded inverse. Resolution increases with $j$ here, as in the 1989 paper; texts that index the spaces by the scale $2^j$ write $V_{j+1} \subset V_j$ instead.
