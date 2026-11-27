# Haldane linearisation and diagonalisation of discrete-time single-crossover recombination

**Model.** Sites $0,1,\dots,n$ carry types from finite sets $X_0,\dots,X_n$; the $n$ links between neighbouring sites form the set $L=\{\tfrac12,\tfrac32,\dots,n-\tfrac12\}$. A population is a probability measure $p$ on $X=X_0\times\dots\times X_n$. For a link $\alpha$, the *recombinator* $R_\alpha(p)=(\pi_{<\alpha}p)\otimes(\pi_{>\alpha}p)$ replaces $p$ by the product of its marginals left and right of $\alpha$; for $G\subseteq L$, $R_G$ is the composition over $\alpha\in G$. In discrete time with *single crossovers*, an offspring is a crossover at link $\alpha$ with probability $\rho_\alpha>0$ for every link $\alpha\in L$, with $\sum_\alpha\rho_\alpha\le1$, giving

$$p_{t+1}=\Phi(p_t):=p_t+\sum_{\alpha\in L}\rho_\alpha\bigl(R_\alpha-\mathbb 1\bigr)(p_t).$$

The *linkage-disequilibrium operators* are $T_G=\sum_{H\supseteq G}(-1)^{|H\setminus G|}R_H$, so $R_H=\sum_{G\supseteq H}T_G$ (Möbius inversion).

**Theorem (linearisation).** For every $G\subseteq L$,

$$T_G\circ\Phi=\sum_{K\supseteq G}z(G,K)\,T_K$$

with explicit coefficients; in particular $z(\varnothing,\varnothing)=1-\sum_\alpha\rho_\alpha$, and $z(G,K)$ factorizes over the segments $I_0^G,\dots,I_{|G|}^G$ into which $G$ cuts $L$.

**Theorem (diagonalisation).** The triangular system has eigenvalues

$$\lambda_G=z(G,G)=\prod_{i=0}^{|G|}\Bigl(1-\sum_{\alpha\in I_i^G}\rho_\alpha\Bigr),$$

the probability of no further crossover inside any segment, and $\lambda_G<\lambda_H$ for $G\subsetneq H$ (this strict ordering, which makes the recursion for $c(G,H)$ well defined, uses $\rho_\alpha>0$ for every link). The operators $U_G=\sum_{H\supseteq G}c(G,H)T_H$ with $c(G,G)=1$ and

$$c(G,H)=\frac{\sum_{H\supsetneq K\supseteq G}c(G,K)\,z(K,H)}{\lambda_G-\lambda_H}\qquad(H\supsetneq G)$$

satisfy $U_G\circ\Phi=\lambda_GU_G$. Hence $p_t=\sum_Ga_G(t)R_G(p_0)$ with

$$a_G(t)=\sum_{M\subseteq G}(-1)^{|G\setminus M|}\sum_{H\subseteq M}\sum_{K\subseteq H}c(H,M)\,\lambda_H^t\,c^*(K,H),$$

where $c^*$ are the coefficients of the inverse transformation. If every segment of $G$ contains at most two links, $T_G$ is already an eigenvector: $T_G(\Phi(p))=\lambda_GT_G(p)$.

**Limit.** $p_t\to R_L(p_0)=\bigotimes_{i=0}^n\pi_ip_0$ (linkage equilibrium) exponentially fast.

## Depends on

## Proof depends on

## Expansion

In continuous time the flow commutes with every recombinator and the solution is $\sum_G\tilde a_G(t)R_G(p_0)$ with product-form coefficients $\prod_{\alpha\notin G}e^{-\tilde\rho_\alpha t}\prod_{\beta\in G}(1-e^{-\tilde\rho_\beta t})$. In discrete time $[R_G,\Phi]\ne0$ unless $L\setminus G$ is contiguous, because two crossovers in one generation cannot occur but can occur over two generations. The commutator is computed explicitly, giving the triangular linear system in the $T_G$; triangularity and distinct eigenvalues make the diagonalisation possible, though the coefficients $c(G,H)$ must be computed recursively rather than in closed form.

## Sources

- Ute von Wangenheim, Ellen Baake and Michael Baake, "Single–crossover recombination in discrete time", arXiv:0906.1678 (2009), Sections 3–7 (closed solution in continuous time; linearisation via the commutator; diagonalisation, eigenvalues $\lambda_G$, recursion for $c(G,H)$ and Proposition 7), <https://doi.org/10.48550/arXiv.0906.1678>; published in *Journal of Mathematical Biology* 60 (2010) 727–760, <https://doi.org/10.1007/s00285-009-0277-4>. The positivity assumption on every $\rho_\alpha$ is that of Section 2 of the source, used in Lemma 5.
