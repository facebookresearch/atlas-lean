# Incomplete Beta-coalescent from truncated offspring numbers

Consider a haploid population of fixed size $N$ in non-overlapping generations (Schweinsberg's model with an upper bound). In each generation the $N$ individuals independently produce $X_1^N,\dots,X_N^N$ potential offspring, i.i.d. copies of $X^N$, and $N$ of the $S_N=\sum_i X_i^N$ potential offspring are sampled without replacement to form the next generation (if $S_N<N$ the population is unchanged). Assume $1<\alpha<2$ and that $X^N$ is supported on $\{0,1,\dots,\psi(N)\}$ with

$$\Big(\tfrac{1}{k^\alpha}-\tfrac{1}{(k+1)^\alpha}\Big)g(k)\le\mathbb P(X^N=k)\le\Big(\tfrac{1}{k^\alpha}-\tfrac{1}{(k+1)^\alpha}\Big)f(k),\qquad 1\le k\le\psi(N),$$

where $f(k),g(k)\to f_\infty=g_\infty>0$ and $m_N=\mathbb E[X^N]\to m_\infty>1$. Let $c_N$ be the probability that two individuals share a parent in the previous generation and $\xi^{n,N}$ the ancestral partition of a sample of size $n$, run on the time scale $\lfloor t/c_N\rfloor$. As $N\to\infty$ the limit depends on the truncation $\psi(N)$:

1. If $\psi(N)/N\to 0$, the limit is Kingman's coalescent restricted to $[n]$.
2. If $\psi(N)/N\to K\in(0,\infty)$, the limit is the $\Lambda$-coalescent without Kingman component whose measure is the **incomplete Beta** law

$$\Lambda(dx)=\frac{\mathbf 1_{\{0<x\le K/(m_\infty+K)\}}}{B\big(\tfrac{K}{m_\infty+K};2-\alpha,\alpha\big)}\,x^{1-\alpha}(1-x)^{\alpha-1}\,dx,\qquad B(p;a,b)=\int_0^p t^{a-1}(1-t)^{b-1}dt,$$

so no single family can exceed the fraction $K/(m_\infty+K)$ of a generation.
3. If $\psi(N)/N\to\infty$, the limit is the complete Beta$(2-\alpha,\alpha)$-coalescent.

The time scale is governed by $\mathcal C_N=N\,\mathbb E\big[X_1^N(X_1^N-1)S_N^{-2}\mathbf 1_{\{S_N\ge N\}}\big]$: in cases 2 and 3, $N^{\alpha-1}\mathcal C_N$ converges to a positive constant, while in case 1, $N\psi(N)^{\alpha-2}\mathcal C_N$ does. Moreover, the prelimiting merger rates match the limit only while the number of active lineages is $o(\sqrt N)$: when at least $\sqrt N$ lineages are present, large mergers occur less often than the limiting rates predict, so very large samples see a different tree topology.

## Expansion

A family of $k$ potential offspring takes a fraction close to $k/(k+S_N-k)\approx k/(k+Nm_N)$ of the next generation. With $\mathbb P(X^N\ge k)\approx f_\infty k^{-\alpha}$, the change of variables $x=k/(k+Nm_\infty)$ turns the law of the largest family fraction into the density $x^{1-\alpha}(1-x)^{\alpha-1}$, cut off at $x=\psi(N)/(\psi(N)+Nm_\infty)$. If $\psi(N)\ll N$ no family takes a positive fraction, simultaneous large mergers vanish and only pairwise mergers survive, giving Kingman's coalescent on the slower time scale. The $\sqrt N$ threshold comes from an $O(k^2/N)$ error in the merger probabilities of $k$ lineages, which always has negative sign.

## Depends on

- [The Beta-coalescent measure on the unit interval](beta-lambda.md)

## Sources

- Jonathan A Chetwynd-Diggle, Bjarki Eldon, "Beta-coalescents when sample size is large", arXiv:2601.08538 (2026), Propositions 3.2, 3.3 and 3.4, Lemma 3.6, Corollary 3.7, <https://doi.org/10.48550/arXiv.2601.08538>
