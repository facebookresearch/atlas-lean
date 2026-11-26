# Universal coalescent tree of generalized logistic branching

**Model.** For each $\kappa\in\mathbb{N}$ (the carrying-capacity index) a population starts from one individual; while its size is $n$, each individual is independently replaced by $i\ge0$ offspring at rate $\Lambda_i^{\kappa,n}\ge0$, with $\sup_{\kappa,n}\sum_i i^2\Lambda_i^{\kappa,n}<\infty$. There are intrinsic rates $\Lambda_i^\infty$ with $\bar\Lambda^\infty=\sum_i(i-1)\Lambda_i^\infty>0$ and $\sup_{n\le n_\kappa}\sum_i|\Lambda_i^{\kappa,n}-\Lambda_i^\infty|\to0$ for some $n_\kappa\to\infty$. The sampling time $T_\kappa$ is a stopping time with $T_\kappa\to\infty$ in distribution, and growth is superlinear before it: with probability tending to one, the per-capita growth rate stays above $c\,N_\kappa(t)^{-\alpha}$ for some $c>0$, $\alpha\in(0,1)$ on $[0,T_\kappa]$. Examples: exponential growth; logistic growth with competition deaths $\Lambda_0^{\kappa,n}=\Lambda_0^\infty+\frac n\kappa\bar\Lambda^\infty$ sampled when $N$ first reaches $x\kappa$, $x\in(0,1)$; Gompertz growth with $\frac{\log n}{\log\kappa}$ in place of $\frac n\kappa$; logistic growth with reduced reproduction.

**Coalescent tree.** On $\{N_\kappa(T_\kappa)\ge m\}$, sample $m$ individuals uniformly without replacement at $T_\kappa$ and let $\pi_\kappa(t)$ be the partition of $\{1,\dots,m\}$ in which $i,j$ share a block iff the sampled individuals have a common ancestor alive at time $t$.

**Theorem.** As $\kappa\to\infty$, $\pi_\kappa$ on $\{N_\kappa(T_\kappa)\ge m\}$ converges in finite-dimensional distributions to the limit tree $\pi_\infty$ of the density-independent supercritical branching process with rates $\Lambda_i^\infty$. Its law depends only on the intrinsic rates: for $0<t_1<\dots<t_r$ and nested partitions $\gamma_1,\dots,\gamma_r$,
$$\mathbb{P}[\pi_\infty(t_1)=\gamma_1,\dots,\pi_\infty(t_r)=\gamma_r]=\frac{(-1)^me^{-m\bar\Lambda^\infty t_r}}{1-\psi(\infty)}\int_0^\infty\frac{v^{m-1}}{(m-1)!}\prod_{i=0}^{r-1}\prod_{\Gamma\in\gamma_i}H^{b_i(\Gamma)}_{t_i-t_{i-1}}\bigl(\psi(e^{-\bar\Lambda^\infty t_{i+1}}v)\bigr)\prod_{\Gamma\in\gamma_r}\psi^{\#\Gamma}\bigl(e^{-\bar\Lambda^\infty t_r}v\bigr)\,dv,$$
with $\psi$ and $H$ explicit functionals of the limiting branching process. For binary branching the tree has Kingman topology (each merger joins a uniformly chosen pair) independent of $m-1$ explicitly distributed coalescence times.

So the shape of sample genealogies cannot distinguish exponential, logistic or Gompertz growth if sampling happens while growth is still superlinear: coalescences happen early, when density dependence is negligible.

## Expansion

Before the population reaches size $n_\kappa$ it is coupled with a density-independent branching process with rates $\Lambda_i^\infty$. Coalescences of a fixed-size sample occur, with high probability, at times when the population is still small, so they are determined by this exponential phase. After that, the descendant fractions of the early individuals are frozen: superlinear growth makes genetic drift negligible, so the fraction of the population at $T_\kappa$ descending from each early individual converges to its limit under exponential growth. Uniform sampling at $T_\kappa$ then picks ancestors according to these fractions, reproducing the density-independent limit tree.

## Sources

- D. Cheek, "The coalescent tree of a Markov branching process with generalised logistic growth", arXiv:2012.13382 (2020), Section 2 (model, assumptions and examples), Section 3 (Theorem 3.1, limit law of the coalescent tree, Theorem 3.3), Sections 4–7 (coupling with exponential growth, genetic drift, Proposition 5.4, sampling and coalescence), <https://doi.org/10.48550/arXiv.2012.13382>.
