# Moments of the B2 balance index under Yule, uniform and Galton–Watson trees

For a finite rooted phylogeny $N$ with leaf set $L$, let $p_\ell$ be the probability that the simple forward random walk from the root (choosing each outgoing edge uniformly) ends at leaf $\ell$. The Shao–Sokal **$B_2$ index** is the Shannon entropy

$$B_2(N)=-\sum_{\ell\in L}p_\ell\log_2p_\ell,\qquad 0\le B_2(N)\le\log_2 n .$$

For a rooted binary tree with leaf depths $\delta_\ell$, $p_\ell=2^{-\delta_\ell}$ and $B_2(T)=\sum_\ell\delta_\ell2^{-\delta_\ell}$; if $T=T'\oplus T''$ is formed by joining two subtrees at a new root, $B_2(T)=\frac12(B_2(T')+B_2(T''))+1$.

**Theorem.**

*(1)* (Markov branching trees) If $T_n$ is a Markov branching tree with root-split distributions $(q_n)$, symmetric in the sense $q_n(k)=q_n(n-k)$ as in the source's definition, $K_n\sim q_n$, and $\mu_n=\mathbb E[B_2(T_n)]$, $v_n=\operatorname{Var}B_2(T_n)$, then $\mu_1=v_1=0$ and

$$\mu_n=\mathbb E[\mu_{K_n}]+1,\qquad v_n=\tfrac14\operatorname{Var}\big(\mu_{K_n}+\mu_{n-K_n}\big)+\tfrac12\mathbb E[v_{K_n}].$$

*(2)* (Yule / equal-rate Markov model) $\displaystyle\mathbb E[B_2(T_n)]=\sum_{k=1}^{n-1}\frac1k$ and $\operatorname{Var}B_2(T_n)\to2-\pi^2/6$ as $n\to\infty$.

*(3)* (Uniform / PDA model on rooted binary trees with $n$ labeled leaves) $\mathbb E[B_2(T_n)]=\dfrac{3(n-1)}{n+1}$ and $\operatorname{Var}B_2(T_n)\to4/9$.

*(4)* (Galton–Watson trees) For a time-inhomogeneous Galton–Watson tree with offspring law $Y_t$ in generation $t$, $\alpha_t=\mathbb P(Y_t>0)$ and $\eta_t=\mathbb E[\log_2(Y_t)\mathbf 1_{Y_t>0}]$, the tree truncated at generation $k$ satisfies

$$\mathbb E[B_2(T_{\le k})]=\sum_{t=0}^{k-1}\eta_t\prod_{s=0}^{t-1}\alpha_s .$$

For the critical binary tree ($\mathbb P(Y=0)=\mathbb P(Y=2)=\tfrac12$), $\operatorname{Var}B_2(T_{\le k})=\tfrac43-2^{-k+2}+4^{-k}(k+\tfrac83)$, so $\operatorname{Var}B_2(T)=4/3$.

Over all rooted binary trees with $n$ leaves, $2-2^{-n+2}\le B_2(T)\le\lfloor\log_2n\rfloor+(n-2^{\lfloor\log_2n\rfloor})/2^{\lfloor\log_2n\rfloor}$, the minimum being attained only by the caterpillar and the maximum exactly by trees whose leaf depths differ by at most one.

## Expansion

The root-split recursion makes $B_2$ additive in expectation over Markov branching models: conditioning on the root split gives $\mu_n=\frac12(\mathbb E\mu_{K_n}+\mathbb E\mu_{n-K_n})+1$, which simplifies by symmetry of $K_n$ and $n-K_n$. Under the Yule model $K_n$ is uniform on $\{1,\dots,n-1\}$, and the recursion solves to the harmonic number $H_{n-1}$. Under the uniform (PDA) model the split law is the Catalan-type distribution, which gives the rational mean $3(n-1)/(n+1)$. Unlike the integer-valued Colless and Sackin indices, $B_2$ is defined through a random walk and therefore applies verbatim to phylogenetic networks; it also takes at least $2^{\lfloor n/2\rfloor-1}$ distinct values on binary trees with $n$ leaves, so it separates tree shapes more finely.

## Sources

- François Bienvenu, Gabriel Cardona, Celine Scornavacca, "Revisiting Shao and Sokal's $B_2$ index of phylogenetic balance", arXiv:2010.08079 (2020), Definition 1.2 ($B_2$), Propositions 1.7–1.8, Corollary 1.12, Theorem 2.3, Theorem 3.1 and Proposition 3.3 (Galton–Watson trees), Theorem 3.4 (Markov branching trees), Theorems 3.7 and 3.9 (Yule and PDA models), numbering of v2, <https://doi.org/10.48550/arXiv.2010.08079>.
