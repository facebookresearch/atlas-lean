# Constant-size TMRCA discretization: atomic and density embedding errors

Fix $K\ge1$ and a finite, possibly nonuniform grid $0=\tau_0<\cdots<\tau_K$. Write $\Delta_i=\tau_{i+1}-\tau_i$ and $h=\max_{i<K}\Delta_i$. For the probability law $\mu=\mathrm{Exp}(1)$, let $\pi_i=e^{-\tau_i}-e^{-\tau_{i+1}}$ for $i<K$ and $\pi_K=e^{-\tau_K}$. These are the exactly stationary interval masses in the [ideal constant-size stationary-kernel construction](pairwise-smc-hmm-psmc-discretized-tmrca-hidden-s.md), not an assertion about the finite-step approximated PSMC stationary distribution. The error statements below concern probability-law embeddings of these masses, independently of a transition kernel.

Use the normalized total-variation distance $d_{\mathrm{TV}}(\eta,\mu)=\sup_B|\eta(B)-\mu(B)|$, equal to half the density $L^1$ distance when both laws have densities. Thus its maximal value for probability laws is one, not two.

## Atomic embedding

Place each interval mass, including the entire tail, at its left endpoint:

$$A=\sum_{i=0}^K\pi_i\delta_{\tau_i},\qquad \sum_{i<K}\pi_i=1-e^{-\tau_K},\qquad\sum_{i\le K}\pi_i=1.$$

The two sum identities telescope. The finite set $\{\tau_0,\ldots,\tau_K\}$ has $A$-mass one and exponential mass zero. Therefore $A$ and $\mu$ are mutually singular and $d_{\mathrm{TV}}(A,\mu)=1$ for every such grid.

The exponential distribution function on the **whole real line** is $F(x)=0$ for $x<0$ and $F(x)=1-e^{-x}$ for $x\ge0$. With $F_A(x)=A(({-\infty},x])$, the exact Kolmogorov distance is

$$d_K(A,\mu)=\sup_{x\in\mathbb R}|F_A(x)-F(x)|=\max\left(\max_{i<K}\pi_i,\ e^{-\tau_K}\right)\le\max(1-e^{-h},e^{-\tau_K}).$$

For $x<0$ both distribution functions vanish. For $x\in[\tau_i,\tau_{i+1})$ with $i<K$, the difference is $e^{-x}-e^{-\tau_{i+1}}\ge0$, with maximum $\pi_i$ attained at $x=\tau_i$. For $x\ge\tau_K$, it is $e^{-x}$, with maximum $e^{-\tau_K}$ attained at $\tau_K$. Finally, $\pi_i=e^{-\tau_i}(1-e^{-\Delta_i})\le1-e^{-h}$. The negative half-line cannot be handled by the formula $1-e^{-x}$, which is not a distribution function there.

For any sequence of finite grids, allowing the number of intervals to vary, this formula gives

$$d_K(A_n,\mu)\longrightarrow0\quad\Longleftrightarrow\quad\tau_{K_n}^{(n)}\longrightarrow\infty\ \text{ and }\ \max_{i<K_n}\pi_i^{(n)}\longrightarrow0.$$

Hence $h_n\to0$ together with $\tau_{K_n}^{(n)}\to\infty$ suffices for Kolmogorov, and therefore weak, convergence, while total variation remains one. Vanishing maximum mesh is **not necessary**. For integer $n$, take spacing $1/n$ on $[0,n]$ and one final finite interval $[n,2n]$, followed by the unbounded tail. Then $h_n=n$, but the largest finite-interval mass is at most $\max(1-e^{-1/n},e^{-n})\to0$ and the tail mass is $e^{-2n}\to0$.

On the grid $0,0.1,\ldots,1$, the exact distance is $e^{-1}\approx0.367879$, attained at $x=1$, not $1-e^{-0.1}\approx0.095163$. This exhibits the necessity of accounting for the collapsed tail.

## Density embedding with an exact tail

Instead of atoms, distribute each finite-interval mass uniformly within its interval, while retaining the **exact exponential density** on the tail:

$$f(x)=\begin{cases}0,&x<0,\\\pi_i/\Delta_i,&x\in[\tau_i,\tau_{i+1}),\ i<K,\\e^{-x},&x\ge\tau_K.\end{cases}$$

This is a probability density and has the prescribed mass on every interval. Let $H$ be its law. On a finite interval, its height is the average of $e^{-x}$ and lies between $e^{-\tau_{i+1}}$ and $e^{-\tau_i}$. Therefore

$$\int_{\tau_i}^{\tau_{i+1}}|f(x)-e^{-x}|\,dx\le\Delta_i(e^{-\tau_i}-e^{-\tau_{i+1}})\le h\pi_i.$$

The tail contributes zero. Summing and using the telescoping identity gives

$$d_{\mathrm{TV}}(H,\mu)\le\frac h2(1-e^{-\tau_K})\le\frac h2.$$

This bound applies to nonuniform grids too. Unlike the atomic embedding, a density embedding with the exact tail does not require $\tau_K\to\infty$ for convergence when $h\to0$.

For an exact real-valued check of the density error, set $m_i=(1-e^{-\Delta_i})/\Delta_i$. The exponential and the interval-average density cross once, so the contribution of interval $i$ to total variation is $e^{-\tau_i}(1-m_i+m_i\log m_i)$. On the grid $0,0.1,\ldots,1$, the bound is $0.05(1-e^{-1})\approx0.031606$. On the nonuniform grid with 100 intervals of length $0.001$ up to $0.1$, followed by $[0.1,0.2]$ and $[0.2,0.3]$, the exact-error formula gives approximately $0.00206185$, below the bound $0.05(1-e^{-0.3})\approx0.012959$.

If $K=0$, treat it separately without taking a maximum over an empty family: the atomic law is $\delta_0$ and has both distances equal to one, while the density embedding is exactly exponential. The statements concern the constant-size marginal only. They do not bound transition-kernel, observation-likelihood, demographic-estimation or SMC-versus-ARG errors.

## Depends on

- [Stationary-kernel discretization for pairwise SMC hidden Markov models](pairwise-smc-hmm-psmc-discretized-tmrca-hidden-s.md)

## Sources

- H. Li and R. Durbin, *Inference of human population history from individual whole-genome sequences*, Nature 475 (2011), 493–496, <https://pmc.ncbi.nlm.nih.gov/articles/PMC3154645/>, Online Methods, time intervals and discretization. This supplies the modeling context, not the error theorem. The exact Kolmogorov formula, convergence criterion and density-embedding bound are mathematical derivations for the specified embeddings.
