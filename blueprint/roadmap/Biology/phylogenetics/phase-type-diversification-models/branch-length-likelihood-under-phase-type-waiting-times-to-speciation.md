# Branch-length likelihood under phase-type waiting times to speciation

**Phase-type law.** Let $\{X(t)\}_{t\ge 0}$ be a continuous-time Markov chain on $\{1,\dots,n\}\cup\{n+1\}$ with $n+1$ absorbing, initial row vector $\boldsymbol\alpha$ on the transient states and generator $\begin{pmatrix}\mathbf Q&\mathbf q\\ \mathbf 0&0\end{pmatrix}$, so $\mathbf q=-\mathbf Q\mathbf 1$. The absorption time $Z\sim\mathrm{PH}(\boldsymbol\alpha,\mathbf Q)$ has

$$F_Z(z)=1-\boldsymbol\alpha e^{\mathbf Qz}\mathbf 1,\qquad f_Z(z)=\boldsymbol\alpha e^{\mathbf Qz}\mathbf q,\qquad \mathbb E(Z)=-\boldsymbol\alpha\mathbf Q^{-1}\mathbf 1 .$$

A **Coxian** law has $\boldsymbol\alpha=(1,0,\dots,0)$ and bidiagonal $\mathbf Q$ with $Q_{ii}=-\lambda_i$, $Q_{i,i+1}=p_i\lambda_i$, $0<p_i\le 1$: the chain moves through phases in order and may exit early from any phase.

**Model and likelihood.** Suppose a tree grows by symmetric speciation without extinction, each lineage waiting an independent $\mathrm{PH}(\boldsymbol\alpha,\mathbf Q)$ time until it splits into two new lineages. For a tree $T$ with internal branches (root branch included) of lengths $b_1,\dots,b_k$ and pendant branches of lengths $\tilde b_1,\dots,\tilde b_\ell$, where $k=\ell-1$, an internal branch contributes the density of its length and a pendant branch the survival probability of its length, so

$$\mathcal L(T\mid\boldsymbol\alpha,\mathbf Q)=\prod_{i=1}^{k}\boldsymbol\alpha e^{\mathbf Qb_i}\mathbf q\;\times\;\prod_{j=1}^{\ell}\boldsymbol\alpha e^{\mathbf Q\tilde b_j}\mathbf 1 ,$$

multiplied by $(\ell-1)!$ when tip permutations are counted. Independent trees multiply. With one exponential phase ($\mathbf Q=-\lambda$) this reduces to the Yule branch-length likelihood $\prod_i\lambda e^{-\lambda b_i}\prod_j e^{-\lambda\tilde b_j}$.

## Expansion

Under symmetric speciation both daughters start a fresh, independent phase-type clock, so branch lengths are i.i.d. $\mathrm{PH}(\boldsymbol\alpha,\mathbf Q)$; a pendant branch is right-censored at the present. The formulas for $F_Z$ and $f_Z$ follow from $\mathbb P(X(z)\text{ transient})=\boldsymbol\alpha e^{\mathbf Qz}\mathbf 1$ and differentiation. Because a Coxian law with increasing or decreasing phase rates is age-dependent, the induced trees are no longer Yule-distributed in shape, which is how the model reaches the low (more imbalanced) values of Aldous' $\beta$ seen in empirical phylogenies.

## Sources

- A. C. Soewongsono, B. R. Holland, M. M. O'Reilly, "The shape of phylogenies under phase-type distributed times to speciation and extinction", Bulletin of Mathematical Biology 84(10) (2022) 118, <https://doi.org/10.1007/s11538-022-01072-w>, PMCID PMC9474389. Definitions 1–2, Theorem 1, Section 2.4, Eqs. (14)–(17).
