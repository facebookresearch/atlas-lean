# Positive recurrence of double-full binary reaction networks

**Setting.** A reaction network $(\mathcal S,\mathcal C,\mathcal R)$ has species $\mathcal S=\{S_1,\dots,S_d\}$, complexes $\mathcal C\subset\mathbb Z^d_{\ge0}$ and reactions $\mathcal R\subset\mathcal C\times\mathcal C$. Its stochastic mass-action model is the continuous-time Markov chain on $\mathbb Z^d_{\ge0}$ that jumps by $y'-y$ at rate

$$\lambda_{y\to y'}(x)=\kappa_{y\to y'}\prod_{i=1}^d\frac{x_i!}{(x_i-y_i)!}\mathbf 1_{\{x_i\ge y_i\}}.$$

The network is *binary* if every complex has total molecularity at most $2$. A *double complex* is one of the form $2S_i$, a *unary complex* one of the form $S_i$, and the network is *double-full* if $2S_i\in\mathcal C$ for every $i$.

**Statement.** Let $(\mathcal S,\mathcal C,\mathcal R)$ be a binary, double-full network in which, for every double complex $2S_i$, the reaction graph contains a directed path from $2S_i$ to a unary complex or to the zero complex $\emptyset$. Then, for every choice of rate constants, every state in a closed irreducible component of the state space is positive recurrent, and from every initial state $x_0$ the time $\tau_{x_0}$ to enter the union of the closed irreducible components has $\mathbb E[\tau_{x_0}]<\infty$.

**Extension.** Let the linkage classes be $\mathcal L_1,\dots,\mathcal L_\ell$ and $1\le m<\ell$. The same conclusion holds for a double-full binary network if, for $i\le m$, $\mathcal L_i$ is weakly reversible with only binary complexes and contains species $S,\widetilde S$ (possibly equal) with $S+\widetilde S\in\mathcal C$ and a directed path from $S+\widetilde S$ to a unary or the zero complex, and if every double complex $2S$ either lies in some $\mathcal L_i$ with $i\le m$ or has a directed path to a unary or the zero complex.

## Expansion

The proof is a Foster–Lyapunov argument with $V(x)=\sum_{i=1}^d\bigl(x_i(\ln x_i-1)+1\bigr)$ (convention $0\ln0=0$), controlled along *tier sequences*: sequences of states going to infinity, along which the complexes are partitioned into tiers by the growth rate of their mass-action monomials. Double-fullness forces the fastest-growing tier along every tier sequence to consist of binary complexes, and the path hypothesis provides a descending reaction from that top tier to a unary or zero complex, which yields negative drift of $V$ outside a finite set. A companion theorem of the same paper shows that every weakly reversible binary network with a single linkage class becomes positive recurrent in every state once all in-flows $\emptyset\to S$ and out-flows $S\to\emptyset$ are added.

## Sources

- David F. Anderson and Jinsu Kim, "Some Network Conditions for Positive Recurrence of Stochastically Modeled Reaction Networks", SIAM Journal on Applied Mathematics 78 (2018), 2692–2713, <https://doi.org/10.1137/17m1161427>; numbering as in arXiv:1710.11263: Theorem 2.2 (double-full networks), Theorem 5.4 (extension through weakly reversible linkage classes), Theorem 2.1 (companion result), Section 3 (tier structures).
