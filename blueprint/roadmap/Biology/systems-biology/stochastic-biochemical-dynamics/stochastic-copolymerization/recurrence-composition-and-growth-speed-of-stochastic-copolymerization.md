# Recurrence, composition and growth speed of stochastic copolymerization

**Setting.** A polymer is a finite word over monomer types $\mathcal M=\{M_1,\dots,M_d\}$, the empty word being the root. The **copolymerization process** is the continuous-time Markov chain $X(t)$ on the tree of words in which a monomer $M_i$ attaches to the end of the current polymer at rate $k_i^+>0$, independently of the polymer, and the last monomer detaches at rate $k_i^->0$ if it is of type $M_i$. Let $|X(t)|$ be the polymer length, $\sigma_i(t)$ the fraction of type-$i$ monomers in $X(t)$, and

$$\alpha=\sum_{i=1}^d\frac{k_i^+}{k_i^-}.$$

**Theorem 3.1 (recurrence criterion).** $X$ is positive recurrent if $\alpha<1$, null recurrent if $\alpha=1$, and transient if $\alpha>1$.

**Theorem 4.1 (limiting composition).** If $\alpha>1$, then for each $i$, almost surely,

$$\lim_{t\to\infty}\sigma_i(t)=\bar\sigma_i=\frac{k_i^+}{m+k_i^-},$$

where $m>0$ is the unique solution of $\sum_{r=1}^d k_r^+/(m+k_r^-)=1$.

**Theorem 5.1 (growth velocity).** If $\alpha>1$, then almost surely

$$v=\lim_{t\to\infty}\frac{|X(t)|}{t}=\sum_{r=1}^dk_r^+-\sum_{r=1}^dk_r^-\,\bar\sigma_r\in(0,\infty).$$

## Expansion

The chain is a nearest-neighbour random walk on a $d$-ary tree, and it is reversible: the measure $\mu(x)=\prod_{\text{letters } M_i\text{ of }x}k_i^+/k_i^-$ satisfies detailed balance, and its total mass $\sum_{n\ge0}\alpha^n$ is finite exactly when $\alpha<1$; at $\alpha=1$ the walk is null recurrent and for $\alpha>1$ it escapes along a random infinite branch. In the transient case let $F_i$ be the probability that a polymer ending in $M_i$ ever loses that last monomer; first-step analysis gives $F_i=k_i^-/\bigl(k_i^-+\sum_rk_r^+(1-F_r)\bigr)$, solved by $F_i=k_i^-/(m+k_i^-)$ (Propositions 4.3 and 4.4). The sequence of permanently attached monomers is a Markov chain whose stationary law is $\bar\sigma$ (Theorem 4.2, Proposition 4.5), which yields the composition. The velocity is total attachment flux minus detachment flux, the detachment rates being weighted by $\bar\sigma$; its proof goes through Green-function ratios between neighbouring words and a renewal argument along the escape branch (Propositions 5.6-5.13).

## Sources

- D. F. Anderson, J. Ma, P. Gagrani, "Mathematical analysis for a class of stochastic copolymerization processes", *Bulletin of Mathematical Biology* 88(2) (2026), 15, Theorem 3.1, Theorems 4.1 and 4.2, Propositions 4.3-4.5, Theorem 5.1, <https://doi.org/10.1007/s11538-025-01585-0> (preprint arXiv:2510.05383).
