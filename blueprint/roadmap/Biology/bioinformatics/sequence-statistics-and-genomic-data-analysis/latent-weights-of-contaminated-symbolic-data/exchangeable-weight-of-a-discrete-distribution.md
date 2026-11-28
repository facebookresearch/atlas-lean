# Exchangeable weight of a discrete distribution

**Latent weight.** Let $\mathcal{P}$ be the probability measures on a finite set $\Omega$ and $\mathcal{Q}\subseteq\mathcal{P}$ a nonempty model class. The *latent weight* of $\mathcal{Q}$ in $P\in\mathcal{P}$ is

$$\lambda_{\mathcal{Q}}(P)=\sup\{\lambda\in[0,1]:\ P\ge\lambda Q\text{ pointwise for some }Q\in\mathcal{Q}\},$$

the largest fraction of $P$ that can be explained by a model in $\mathcal{Q}$ when the rest is arbitrary contamination: $P=\lambda Q+(1-\lambda)R$. Nonemptiness makes $\lambda=0$ feasible, so the supremum is over a nonempty set. For nonempty closed $\mathcal{Q}$: $\lambda_{\mathcal{Q}}(P)=1$ iff $P\in\mathcal{Q}$, and

$$\lambda_{\mathcal{Q}}(P)=\max_{Q\in\mathcal{Q}}\ \min_{\omega:\,Q(\omega)>0}\frac{P(\omega)}{Q(\omega)},$$

with the maximum attained by some $Q\in\mathcal{Q}$; the inner minimum ranges only over the support of $Q$, which is nonempty because $Q$ is a probability measure. Equivalently, set $P(\omega)/Q(\omega)=+\infty$ for **every** $\omega$ with $Q(\omega)=0$, including when $P(\omega)=0$. For example, with $P=Q=(1,0)$ on two outcomes and $\mathcal{Q}=\{Q\}$ the weight is $\min\{1/1\}=1$, and no $0/0$ arises.

**Exchangeable weight.** Take $\Omega=\mathcal{X}^d$ (for example $d$ CpG sites read on one DNA fragment, $\mathcal{X}$ = methylated/unmethylated) and $\mathcal{Q}=\mathcal{E}$, the exchangeable distributions. For $x\in\mathcal{X}^d$ let $[x]$ be its orbit under coordinate permutations. Then

$$\lambda_{\mathcal{E}}(P)=\sum_{x\in\mathcal{X}^d}\min_{y\in[x]}P(y)=\sum_{z\in[\mathcal{X}^d]}|z|\cdot\min_{x\in z}P(x),$$

and if $\lambda_{\mathcal{E}}(P)>0$ the exchangeable component is unique: $Q(x)=\min_{y\in[x]}P(y)/\lambda_{\mathcal{E}}(P)$.

**Properties.**
1. If $P=\beta Q'+(1-\beta)R'$ with $Q'$ exchangeable and $\lambda_{\mathcal{E}}(R')=0$, then $\lambda_{\mathcal{E}}(P)=\beta$.
2. Marginalizing cannot decrease the weight: $\lambda_{\mathcal{E}}(P)\le\lambda_{\mathcal{E}}(P_I)$ for every nonempty coordinate set $I$; equality forces the exchangeable component of $P_I$ to be $d$-extendable.
3. Lumping symbols coordinatewise by a map $r:\mathcal{X}\to\mathcal{Y}$ cannot decrease the weight.
4. *(Inference.)* For the plug-in estimator $\hat\lambda_n$ from $n$ i.i.d. samples, $\sqrt n(\hat\lambda_n-\lambda)$ converges in law to $\sum_z|z|\min_{x\in C_z}Z_z^{(x)}$, where $C_z$ is the set of minimizers of $P$ in the orbit $z$ and $Z$ is the multinomial Gaussian limit. If each orbit has a unique minimizer the limit is a centered normal, and the bootstrap of $\sqrt n(\hat\lambda^*-\hat\lambda)$ is then consistent.

## Expansion

The supremum formula follows because $P\ge\lambda Q$ is equivalent to $\lambda\le P(\omega)/Q(\omega)$ for all $\omega$ with $Q(\omega)>0$ (the constraint is vacuous where $Q(\omega)=0$); attainment uses compactness of the nonempty closed class and upper semicontinuity of $Q\mapsto\min_{Q(\omega)>0}P(\omega)/Q(\omega)$. An exchangeable $Q$ is constant on each orbit, so $\lambda Q(x)\le\min_{y\in[x]}P(y)$, and taking $\lambda Q$ equal to these orbit minima is feasible and optimal, which gives the closed form. Marginalization and lumping map exchangeable measures to exchangeable measures and preserve the domination $P\ge\lambda Q$, giving the monotonicity properties. The estimator is a sum of minima of empirical frequencies; minima of jointly Gaussian fluctuations over tied minimizers give the non-normal limit, which becomes normal when ties are absent. Applied to methylation reads, a weight well below one indicates patterns overrepresented beyond what exchangeable (site-symmetric) methylation plus contamination explains.

## Sources

- A. Pearson, M. E. Lladser, "On Contamination of Symbolic Datasets", arXiv:2002.05592 (2020), Section 2 (definition of latent weight and its characterizations), Section 3 (exchangeable weights: closed form, uniqueness, mixtures, marginals and lumping), Section 4 (asymptotic law of the estimator, unique-minimizer normal limit and bootstrap consistency), Section 5 (DNA methylation analysis), <https://doi.org/10.48550/arXiv.2002.05592>.
