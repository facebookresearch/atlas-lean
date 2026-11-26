# Exact linear lumping of mass-action networks

**Setting.** Consider a parameter-dependent reaction network ODE $\dot x=F(x,k)$ on $\mathbb R^n$ with mass-action kinetics, $F(x,k)=\sum_{i=1}^dk_i\,x^{m^{(i)}}v_i$, where reaction $i$ has reactant (source) exponent vector $m^{(i)}\in\mathbb Z^n_{\ge0}$, reaction vector $v_i$ and rate constant $k_i>0$. A surjective linear map $T:\mathbb R^n\to\mathbb R^r$, $r<n$, is an **exact linear lumping** at parameter $k^*$ if there is a map $G$ with $T\,F(x,k^*)=G(Tx)$ for all $x$, so the lumped variables $y=Tx$ obey the closed system $\dot y=G(y)$. A parameter set is *generic* if it contains a nonempty open subset of parameter space; parameters at which additional lumpings appear are *critical*.

**Proposition 1 and Corollary 1 (Jacobian criterion).** $T$ is a lumping map at $k^*$ if and only if $DF(x,k^*)(\ker T)\subseteq\ker T$ for every $x\in\mathbb R^n$, equivalently $DF(x,k^*)^{\mathsf T}(\operatorname{im}T^{\mathsf T})\subseteq\operatorname{im}T^{\mathsf T}$ for every $x$.

**Proposition 2 (single reaction).** For a single reaction $\dot x=k\,x^{m}v$, a subspace $W$ is invariant under every Jacobian $DF(x)$ if and only if either (Type 1) $W$ is spanned by coordinate directions of species that are not reactants ($m_i=0$), or (Type 2) $v\in W$.

**Propositions 3 and 4, Corollary 3 (generic networks).** If $T$ is a lumping map for all parameters in a generic set, then $T$ lumps each single-reaction system $\dot x=k_ix^{m^{(i)}}v_i$ separately, so $\ker T$ is of Type 1 or Type 2 for every reaction. Consequently, for generic parameters every exact linear lumping is, up to row operations, a combination of the two obvious reductions: *eliminating non-reactant species* (keeping the coordinates of the remaining species) and *projecting along stoichiometric first integrals* (quotienting by reaction vectors). The same characterization holds for product-form kinetics such as Michaelis-Menten and Hill rate laws.

**Proposition 5 (critical parameters).** For a fixed rank and reduced row echelon form of $T$, the entries of $T$ and the critical parameter values $k^*$ at which $T$ becomes a lumping solve a polynomial system that is linear in $k^*$; nontrivial lumpings occur only on these algebraic subsets of parameter space.

## Expansion

Since $T$ is linear, $TF=G\circ T$ means $F$ maps fibres $x+\ker T$ into fibres, which is the Jacobian invariance condition. For one reaction the Jacobian is $k\,v\,\nabla(x^m)^{\mathsf T}$, a rank-one matrix whose image is spanned by $v$ and whose kernel contains the non-reactant directions, so an invariant subspace must either contain $v$ or be killed by $\nabla(x^m)$ for all $x$. For generic rate constants the monomials of distinct reactions are linearly independent functions, so invariance for the sum forces invariance for each summand. At special parameter values cancellations between reactions create further lumpings, as in the self-replication and two-pathway enzyme case studies, and proper lumpings (partitions of species into blocks) have block-sum criteria on the Jacobian (Proposition 6).

## Sources

- J. Eilertsen, V. G. Romanovski, S. Schnell, S. Walcher, "Lumping of reaction networks: generic and critical parameters", arXiv preprint (2026), Proposition 1, Corollary 1, Propositions 2-5, Corollary 3, Proposition 6, <https://doi.org/10.48550/arXiv.2606.28895>.
