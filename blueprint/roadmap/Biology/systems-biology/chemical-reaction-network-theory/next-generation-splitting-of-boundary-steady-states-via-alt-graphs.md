# Next-generation splitting of boundary steady states via ALT-graphs

Consider an integer-valued and binary chemical reaction network $(\mathcal S,\mathcal R)$ (every source and target complex is $0$, $S_i$, $2S_i$ or $S_i+S_j$) with species concentrations $c\in\mathbb R^n_{\ge0}$, dynamics $\dot c=\Gamma R(c)$, and kinetic rate functions satisfying: (K1) $R_k$ is $C^1$; (K2) $R_k(c)>0$ exactly when every reactant of $R_k$ is present; (K3) $\partial R_k/\partial c_i=0$ if $S_i$ is not a reactant; (K4) $\partial R_k/\partial c_i>0$ if $S_i$ is a reactant and all other reactant copies are present; (K5) $\partial R_k/\partial c_i=0$ if $S_i$ is a reactant but some other reactant copy is absent. Mass action satisfies (K1)-(K5).

A nonempty $\mathcal X\subseteq\mathcal S$ is a *siphon* if every reaction producing a species of $\mathcal X$ consumes a species of $\mathcal X$. The species vanishing at a boundary steady state $c^*=(x^*,y^*)$, $x^*=0$, form a siphon, and the face $\{x=0\}$ is invariant. Let $\dot x=f(x,y)=\Gamma' R(x,y)$ be the $\mathcal X$-reduced system and $J=D_xf(x^*,y^*)$.

**$-J$ is a $Z$-matrix.** Under (K1)-(K5), every off-diagonal entry of $J$ is nonnegative.

**ALT-graph.** The autocatalysis-leak-transition graph on $\mathcal X$ has vertices $\mathcal X\cup\{0\}$ and multiset edge labels from $\mathcal R$, assigned from each reduced reaction: autocatalytic $X_i\to2X_i$ labels $e_{ii}$; leak $X_i\to0$ labels $e_{i0}$; transition $X_i\to X_j$ labels $e_{ij}$; and catalytic transitions $X_i\to X_i+X_j$, $X_i\to2X_j$, $X_i\to X_j+X_\ell$ label $e_{ii}$ together with $e_{ij}$ (twice for $2X_j$) or $e_{ij},e_{i\ell}$. Its ALT-matrix $L(\mathcal G)$ has off-diagonal entries $[L]_{ji}=\sum_{R_k\in\phi(e_{ij})}\partial_iR_k$ and diagonal entries $\sum_{\phi(e_{ii})}\partial_iR_k-\sum_{\phi(e_{i0})}\partial_iR_k-\sum_{p\ne i}\sum_{\phi(e_{ip})}\partial_iR_k$, with $\partial_iR_k=\partial R_k(x^*,y^*)/\partial x_i$. Then $L(\mathcal G)=J$, and $L$ is additive over edge-disjoint unions of ALT-graphs.

**Splitting theorem.** A reaction is *autocatalytic* if it labels a loop $e_{ii}$. Call an autocatalytic reaction *critical* if none of its catalytic instances leaves the strongly connected component of its source, and a strongly connected component *critical* if removing at most one outgoing catalytic instance of each autocatalytic reaction disconnects it from $0$. An *autocatalytic decomposition* $\mathcal G=\mathcal G_F\oplus\mathcal G_{-V}$ peels off, one at a time, single autocatalytic instances or autocatalytic-catalytic instance pairs into $\mathcal G_F$. If $\mathcal G_F$ is nonempty and $\mathcal G_{-V}$ contains no critical autocatalytic reaction and no critical strongly connected component, then

$$J=F-V,\qquad F=L(\mathcal G_F)\ \text{nonnegative and nonzero},\qquad -V=L(\mathcal G_{-V}),\ V\ \text{a $Z$-matrix with}\ V^{-1}\ge0.$$

Consequently, if $c^*$ is locally asymptotically stable for the invariant subsystem on its boundary face within the stoichiometric compatibility class $\mathsf C_{c_0}$, then $c^*$ is locally asymptotically stable relative to $\mathsf C_{c_0}$ when $\rho(FV^{-1})<1$ and unstable when $\rho(FV^{-1})>1$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../epidemiology/next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

The siphon property together with (K2) and (K5) means only reactions with exactly one reactant copy in $\mathcal X$ contribute to $J$, which yields the six reaction types encoded in the ALT-graph and the sign pattern of a $Z$-matrix. The splitting places every positive diagonal contribution (autocatalysis) into $F$; what remains in $V$ is a $Z$-matrix whose block-triangular form along strongly connected components has irreducible diagonal blocks with nonnegative nonzero column sums, which guarantees $V^{-1}\ge0$. The stability dichotomy is then the next-generation-matrix threshold theorem applied to the boundary steady state, exactly as for the disease-free equilibrium of an epidemic model.

## Sources

- M. D. Johnston and P. Jarne Cupons, "Autocatalysis and Boundary Stability in Chemical Reaction Systems", arXiv preprint (2026), <https://doi.org/10.48550/arXiv.2610.01636>. Definitions 2.4-2.5 (siphon, reduced system), assumptions (K1)-(K5) in Section 2, Theorems 2.8-2.10, Definitions 3.1-3.2 (ALT-graph and ALT-matrix), Theorem 3.3, Definition 3.5, Definition 3.7, Lemma 3.8 and Theorem 3.10.
