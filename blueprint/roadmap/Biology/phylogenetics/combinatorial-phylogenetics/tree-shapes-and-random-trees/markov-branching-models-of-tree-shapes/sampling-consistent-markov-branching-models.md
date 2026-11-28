# Sampling-consistent Markov branching models

**Setting.** Let $\mathbb T_n$ be the set of rooted binary tree shapes with $n$ labelled tips. Every $\tau\in\mathbb T_n$ ($n\ge2$) splits at the root as $\tau=\tau'\oplus\tau''$, with $\tau'$ carrying $i=\lambda(\tau')$ tips. A family of probability laws $(P_n)_{n\ge1}$ on $\mathbb T_n$ is a *Markov branching model* if there are laws $q_n$ on $\{1,\dots,n-1\}$ with $q_n(i)=q_n(n-i)$ such that

$$P_n(\tau)=\frac{2\,q_n(i)}{\binom ni}\,P_i(\tau')\,P_{n-i}(\tau'').$$

It is *sampling consistent* if, for every $n\ge2$, deleting the tip labelled $n+1$ (and suppressing its parent) from a $P_{n+1}$-tree yields a $P_n$-tree.

**Theorem (classical models).** The uniform distribution on $\mathbb T_n$ (PDA model) and the law of a uniform *ranked* labelled tree with its ranking forgotten (ERM, or Yule–Harding model) are both Markov branching, with

$$q_n^{\rm pda}(i)=\frac12\binom ni\frac{t_i\,t_{n-i}}{t_n},\qquad q_n^{\rm erm}(i)=\frac1{n-1},$$

where $t_n=(2n-3)!!$ is the number of rooted binary trees with $n$ labelled tips. The Yule pure-birth tree stopped at $n$ tips has the ERM shape law, and the Kingman coalescent tree is uniform on ranked labelled trees, so its unlabelled shape has the same law as a Yule tree.

**Theorem (Aldous' beta-splitting family).** For $\beta>-2$, let $q_n^\beta(i)\propto\binom ni B(\beta+i+1,\beta+n-i+1)$. Then

$$P_n^\beta(\tau)=\frac{\Gamma(\beta+2)^n\,2^{n-1}}{\Gamma(\beta+n+1)}\prod_{v}\frac{\Gamma(\beta+\lambda(v)+1)}{\Gamma(\lambda(v)+1)\,a_{\lambda(v)}(\beta)},$$

the product running over internal vertices $v$ with $\lambda(v)$ descendant tips and $a_m(\beta)=\frac{\Gamma(2\beta+m+2)}{\Gamma(m+1)}\int_0^1(1-x^m-(1-x)^m)x^\beta(1-x)^\beta dx$; $\beta=0$ gives ERM and $\beta=-3/2$ gives PDA.

**Theorem (characterization, Haas–Miermont–Pitman–Winkel).** If $(P_n)$ is a sampling-consistent Markov branching model, there is a measure $\mu$ on $[0,1]$, invariant under $x\mapsto1-x$, with $\int_{(0,1)}x(1-x)\,\mu(dx)<\infty$, such that

$$q_n(i)=\alpha_n^{-1}\Big\{\binom ni\int_{(0,1)}x^i(1-x)^{n-i}\mu(dx)+n\mu(\{0\})\mathbf 1_{i=1}+n\mu(\{1\})\mathbf 1_{i=n-1}\Big\},$$

with $\alpha_n=\int_{(0,1)}(1-x^n-(1-x)^n)\mu(dx)+n\mu(\{0,1\})$.

## Expansion

Sampling consistency forces the root splits $(q_n)$ to be those of an exchangeable fragmentation: dropping a uniformly placed tip from a split of $n+1$ into $(i,n+1-i)$ gives a split of $n$, and the resulting consistency equations make the split frequencies a de Finetti mixture of binomial samplings of a random "interval split" $x$, plus possible dust atoms at $0$ and $1$ that peel off single tips. Interval-splitting models (split the unit interval at a point drawn from a density $f$, send uniform tips left or right) are obviously sampling consistent, and the beta-splitting family is the case $f(x)\propto x^\beta(1-x)^\beta$. The PDA rule $q_n^{\rm pda}(i)\to c_{i-1}4^{-i}$ (Catalan numbers) concentrates on very unbalanced splits, while ERM's uniform split puts more weight on balanced trees.

## Sources

- Amaury Lambert, "Probabilistic Models for the (sub)Tree(s) of Life", arXiv:1603.03705: Proposition 2.5 ($t_n=(2n-3)!!$), Propositions 3.4–3.6 (Yule and Kingman shape laws), Definition 4.1 and Theorem 4.4 (PDA and ERM as Markov branching models), Proposition 4.8 (beta-splitting law), Theorem 4.11 (characterization of sampling-consistent Markov branching models). <https://doi.org/10.48550/arXiv.1603.03705> Published version: Brazilian Journal of Probability and Statistics 2017, 31(3) 415-475, <https://doi.org/10.1214/16-BJPS320>.
