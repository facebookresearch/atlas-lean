# Mutant subpopulation sizes in supercritical branching populations under power-law mutation rates

**Model.** Traits are the vertices $V$ of a finite directed graph $(V,E)$ with wild type $0$. A cell of trait $v$ divides at rate $\alpha(v)$ and dies at rate $\beta(v)$, with net growth rate $\lambda(v) = \alpha(v) - \beta(v)$ and $\lambda(0) > 0$; at each division, each daughter independently mutates along an edge $(v,u)$ with probability $\mu^{(n)}(v,u)$. Edges carry labels $\ell(v,u) > 0$ and the *power-law mutation regime* is

$$n^{\ell(v,u)}\,\mu^{(n)}(v,u) \longrightarrow \mu(v,u) \in (0,\infty).$$

Start from one wild-type cell, let $Z^{(n)}_v(t)$ be the number of trait-$v$ cells, $W$ the random variable of the source's construction (its (4.6)): the almost-sure limit of the natural positive martingale of an auxiliary birth–death process with rates $\alpha(0)$, $\beta(0)$ that does not depend on $n$, with law $\mathrm{Ber}(\lambda(0)/\alpha(0))\otimes\mathrm{Exp}(\lambda(0)/\alpha(0))$ (the event $\{W>0\}$ is the long-time survival of the wild-type lineage), and use the time scale $\mathfrak{t}^{(n)}_t = t\log n/\lambda(0)$, at which the wild type reaches size $n^t$. For $v \in V$ let $t(v)$ be the minimal total label along walks from $0$ to $v$, and $\theta(v)$ the maximal number of neutral traits ($\lambda = \lambda(0)$) among the heads $v(1),\dots,v(k)$ of such a minimal walk $(0=v(0),v(1),\dots,v(k)=v)$ (the wild type $v(0)=0$ is not counted).

**Theorem (stochastic exponents).** For $0 < T_1 < T_2$, the exponents $X^{(n)}_v(t) = \lambda(0)\log^+ Z^{(n)}_v(\mathfrak{t}^{(n)}_t)/\log n$ satisfy

$$\big(X^{(n)}_v(t)\big)_{v\in V,\,t\in[T_1,T_2]} \longrightarrow \mathbf{1}_{\{W>0\}}\big(x_v(t)\big)_{v\in V,\,t\in[T_1,T_2]}$$

in probability in $L^\infty$, where each $x_v$ is deterministic, continuous, non-decreasing and piecewise linear, its slope changing only at finitely many times when a new trait starts to grow or a trait is overtaken by a faster-growing ancestor. In particular:

- if $\lambda(v) \le \lambda(0)$ for all $v$, then $x_v(t) = \lambda(0)\,(t - t(v))_+$;
- on the infinite path $0 \to 1 \to 2 \to \cdots$ with $\inf_i \ell(i,i+1) > 0$, $x_i(t) = \lambda_{\max}(i)\,(t - \tilde t(i))_+$ with $\lambda_{\max}(i) = \max_{j\le i}\lambda(j)$ and $\tilde t(i) = \sum_{j<i}\ell(j,j+1)\lambda(0)/\lambda_{\max}(j)$.

**Theorem (first-order sizes, non-increasing growth).** If $\lambda(v) \le \lambda(0)$ for all $v$, then for $t > t(v)$ and $s \in \mathbb{R}$, $Z^{(n)}_v(\mathfrak{t}^{(n)}_t + s)$ is of exact order $n^{t-t(v)}\log^{\theta(v)}(n)\,e^{\lambda(0)s}$: divided by this quantity it converges in probability, uniformly on compact sets, to $W\sum_{\gamma\in A(v)}w_\gamma$, where $A(v)$ is the set of admissible walks from $0$ to $v$ and the weights $w_\gamma$ are explicit, positive and deterministic. On the random time scale at which the wild type (or the total population) first reaches $n^t$, the same holds with $W$ replaced by $\mathbf{1}_{\{W>0\}}$.

## Expansion

The wild type grows like $W e^{\lambda(0)t}$, so at time $\mathfrak{t}_t$ it has produced about $n^{t-\ell}$ mutants along an edge of label $\ell$, each founding a family growing at rate $\lambda(v)$. When no mutant outgrows the wild type, every subpopulation inherits the wild type's growth exponent and appears with delay equal to the cheapest cumulative label $t(v)$; neutral intermediates contribute an extra $\log n$ factor each, because a neutral subpopulation keeps producing the next mutants at a rate proportional to its own size throughout a window of length $\log n$. With faster mutants, the slope of $x_v$ switches to the largest growth rate among its ancestors once that ancestor's contribution dominates, which gives the recursive piecewise-linear description.

## Sources

- Vianney Brouard, "Genetic composition of supercritical branching populations under power law mutation rates", The Annals of Applied Probability 35 (2025), 3717–3772, <https://doi.org/10.1214/25-aap2160>; numbering as in arXiv:2309.12055: Definition of admissible walks, Theorems 2.7 and 2.9, Corollaries 2.10 and 2.12.
