# Devaney chaos of the folding dynamics in the 2D HP lattice protein model

**Setting.** In the two-dimensional hydrophobic–hydrophilic (HP) square-lattice model, a protein of $\mathsf N+1$ residues is a lattice walk, encoded in *absolute encoding* by the directions $C=(C_1,\dots,C_{\mathsf N})\in(\mathbb Z/4\mathbb Z)^{\mathsf N}$ of its successive bonds. Folding at residue $|k|$ rotates the tail of the chain clockwise ($k>0$) or anticlockwise ($k<0$) by one quarter turn:

$$f_k(C)=\big(C_1,\dots,C_{|k|-1},f^{\operatorname{sign}k}(C_{|k|}),\dots,f^{\operatorname{sign}k}(C_{\mathsf N})\big),\qquad f(x)=x+1\pmod4,$$

and $k=0$ leaves $C$ unchanged. A folding process is a sequence $F=(F^n)_{n\ge0}\in[\![-\mathsf N,\mathsf N]\!]^{\mathbb N}$. On the phase space $\mathcal X=\mathfrak S_{\mathsf N}\times[\![-\mathsf N,\mathsf N]\!]^{\mathbb N}$, where $\mathfrak S_{\mathsf N}$ is the set of admissible conformations, the dynamics is

$$X^{n+1}=G(X^n),\qquad G(C,F)=\big(f_{F^0}(C),\ \sigma(F)\big),$$

with $\sigma$ the shift. The metric is $d(X,\check X)=d_C+d_F$, where $d_C(C,\check C)=\sum_{k=1}^{\mathsf N}\delta(C_k,\check C_k)\,2^{\mathsf N-k}$ and $d_F(F,\check F)=\frac{9}{2\mathsf N}\sum_{k\ge0}|F^k-\check F^k|\,10^{-(k+1)}$.

**Theorem.** $G$ is continuous on $(\mathcal X,d)$, and the folding process is:

1. **chaotic in the sense of Devaney**: it is topologically transitive (in fact strongly transitive), and its periodic points are dense (it is regular), which implies sensitive dependence on initial conditions;
2. **sensitive** with constant at least $2^{\mathsf N-1}$;
3. **expansive** with constant at least $1$.

The folding map is a particular chaotic iteration $\tilde G_f$. In general, the chaotic iterations of a map $f:\mathbb B^n\to\mathbb B^n$ are chaotic in Devaney's sense exactly when the iteration graph $\Gamma(f)$ is strongly connected.

## Expansion

The integer part of $d$ records which bond directions differ, weighting early bonds most heavily, since a change at bond $k$ moves the whole tail. The decimal part records how long two folding sequences agree. Transitivity comes from the shift: any target conformation and target sequence prefix can be reached by appending the right moves to any initial segment. Periodic points come from periodic folding sequences returning the chain to its start. Sensitivity is large because a single differing early fold rotates the entire tail, changing $d_C$ by at least $2^{\mathsf N-1}$. Structure prediction methods such as neural networks or genetic algorithms implicitly assume that the outcome of folding is a predictable function of the move sequence, and chaos of the dynamics limits how well such learners can generalize.

## Sources

- Jacques M. Bahi, Nathalie Côté, Christophe Guyeux, Michel Salomon, "Protein Folding in the 2D Hydrophobic-Hydrophilic (HP) Square Lattice Model is Chaotic", arXiv:1608.05855 (2016), Section 3 (dynamical system $G$, metric $d$), Section 4 (continuity, regularity, strong transitivity and the Devaney chaos theorem), Section 5 (characterization via strongly connected iteration graphs) and Section 6 (sensitivity constant $2^{\mathsf N-1}$, expansivity constant $1$), <https://doi.org/10.48550/arXiv.1608.05855>.
