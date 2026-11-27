# Sign-vector criterion for unique complex balancing equilibria of generalized mass action systems

**Setting.** A *generalized mass action system* $(\mathscr{S},\mathscr{C},\tilde{\mathscr{C}},\mathscr{R},k)$ has species $\mathscr{S}=\{1,\dots,n\}$, a reaction graph $\mathscr{R}$ on stoichiometric complexes $y\in\mathscr{C}\subset\mathbb{R}^n_{\ge0}$, a *kinetic-order complex* $\tilde y\in\mathbb{R}^n$ attached to each source complex $y$, and rate constants $k_{y\to y'}>0$. The dynamics is

$$\dot c=\sum_{y\to y'\in\mathscr{R}}k_{y\to y'}\,c^{\tilde y}\,(y'-y),\qquad c\in\mathbb{R}^n_{>0},$$

with $c^{\tilde y}=\prod_ic_i^{\tilde y_i}$; classical mass action is $\tilde y=y$. The *stoichiometric subspace* is $S=\mathrm{span}\{y'-y\}$ and the *kinetic-order subspace* is $\tilde S=\mathrm{span}\{\tilde y'-\tilde y\}$ (over reactions within linkage classes). A *complex balancing equilibrium* $c$ balances inflow and outflow at every complex. For a subspace $U$, $\sigma(U)=\{\mathrm{sign}(u):u\in U\}\subseteq\{-,0,+\}^n$ is its set of sign vectors.

**Statements.**

1. If some generalized mass action system on the network has a complex balancing equilibrium, the network is weakly reversible. For weakly reversible networks the two deficiencies are $\delta=m-l-s$ and $\tilde\delta=m-l-\tilde s$ ($m$ complexes, $l$ linkage classes, $s=\dim S$, $\tilde s=\dim\tilde S$), and if $\tilde\delta=0$ every choice of rate constants admits a complex balancing equilibrium.
2. If the set $\tilde Z$ of complex balancing equilibria is nonempty, then $\tilde Z=\{c\in\mathbb{R}^n_{>0}:\ln c-\ln c^*\in\tilde S^{\perp}\}=\{c^*\circ e^{\tilde v}:\tilde v\in\tilde S^\perp\}$ for any $c^*\in\tilde Z$.
3. *(Uniqueness.)* For subspaces $S,\tilde S$, every positive coset $(c'+S)_{\ge}$ meets $\{c^*\circ e^{\tilde v}:\tilde v\in\tilde S^\perp\}$ in at most one point for all $c^*,c'>0$ if and only if $\sigma(S)\cap\sigma(\tilde S^\perp)=\{0\}$. Conversely, for a weakly reversible network with $\sigma(S)\cap\sigma(\tilde S^\perp)\neq\{0\}$, some rate constants give more than one complex balancing equilibrium in some stoichiometric compatibility class.
4. *(Existence and uniqueness.)* If $\tilde Z\neq\emptyset$, $\sigma(S)=\sigma(\tilde S)$ and $(+,\dots,+)\in\sigma(S^\perp)$, then $\tilde Z$ meets every stoichiometric compatibility class $(c'+S)\cap\mathbb{R}^n_{>0}$ in exactly one point. For classical mass action ($S=\tilde S$) this recovers the Horn-Jackson theorem.

## Depends on

- [Horn–Jackson: one equilibrium per compatibility class](../../complex-balancing-and-the-deficiency-zero-theore/exists-unique-equilibrium-of-is-complex.md)
- [Weakly reversible reaction network](../../../../Dynamics/smooth-dynamics/is-weakly-reversible.md)

## Expansion

Statement 2 is the usual log-linear description of complex balanced equilibria, now with exponents taken from the kinetic-order complexes. Intersecting the toric set $c^*\circ e^{\tilde S^\perp}$ with a compatibility class reduces to the map $F(\lambda)=\sum_kc^*_ke^{\langle\lambda,\tilde w^k\rangle}w^k$ built from bases of $S^\perp$ and $\tilde S^\perp$. Two solutions $c_1\neq c_2$ in one class give $c_1-c_2\in S$ and $\ln c_1-\ln c_2\in\tilde S^\perp$ with the same sign pattern, since $\ln$ is increasing, which is exactly a nonzero common sign vector; this proves the injectivity criterion and, by choosing rates, its sharpness. Surjectivity uses a lattice isomorphism between the face lattices of the sign-vector sets: when $\sigma(S)=\sigma(\tilde S)$ and a positive conservation law exists, $F$ is a real-analytic isomorphism onto the interior of the polyhedral cone, generalizing Fulton's lemma behind Horn-Jackson.

## Sources

- Stefan Müller and Georg Regensburger, "Generalized Mass Action Systems: Complex Balancing Equilibria and Sign Vectors of the Stoichiometric and Kinetic-Order Subspaces", SIAM Journal on Applied Mathematics 72 (2012), 1926–1947, <https://doi.org/10.1137/110847056>; numbering as in arXiv:1209.6488: Section 2 (generalized mass action systems and deficiencies), Section 3 (sign-vector propositions on uniqueness and non-uniqueness, injectivity and surjectivity theorems for $F$, and the main theorem on complex balancing equilibria).
