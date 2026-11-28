# Impossibility of consistent distance estimation from sequence lengths under TKF91

**Model (TKF91).** Sequences are strings over an alphabet preceded by an *immortal link* $\bullet$. In continuous time each non-immortal site is substituted at rate $\nu$ (new state drawn from $\pi$), deleted at rate $\mu$, and every site including $\bullet$ inserts a new site with state drawn from $\pi$ immediately to its right at rate $\lambda$. The length $|\vec x|$ (number of non-immortal sites) is then a linear birth–death process with immigration: births at rate $\lambda(M+1)$ and deaths at rate $\mu M$ from length $M$. For $\lambda<\mu$ its stationary law is geometric, $\Pi(M)=(1-\lambda/\mu)(\lambda/\mu)^M$, with mean $\lambda/(\mu-\lambda)$. On a rooted tree the root sequence is drawn from stationarity and the process runs independently along branches.

**Theorem.** Let $T^1,T^2$ be two-leaf trees (cherries) with heights $h_1>h_2>0$, and let $\mathcal L_i$ be the joint law of the two leaf sequence lengths $(N_1^{(i)},N_2^{(i)})$ under TKF91 on $T^i$ started from stationarity. For every fixed $\mu\in(0,\infty)$,

$$
\limsup_{\lambda\nearrow\mu}\ \|\mathcal L_1-\mathcal L_2\|_{\mathrm{TV}}<1 .
$$

**Corollary.** In the regime where expected sequence length tends to infinity ($\lambda\nearrow\mu$), no estimator based only on leaf sequence lengths identifies the tree height (pairwise distance) with probability tending to one: for any prior giving positive mass to two different heights, $\limsup_{\lambda\nearrow\mu}\sup_f\mathbb P(f(N^T)=T)<1$.

## Expansion

Rescale time so that $\mu=1$. Along a branch of length $t$, each of the $M$ initial sites independently leaves a geometric-like family of descendants whose total has mean $\beta(\lambda,t)=e^{-(1-\lambda)t}$ and variance $\sigma^2(\lambda,t)=\frac{1+\lambda}{1-\lambda}e^{-(1-\lambda)t}\big(1-e^{-(1-\lambda)t}\big)$, both bounded away from $0$ and $\infty$ as $\lambda\to1$ for fixed $t$. With the root length $M$ of order $1/(1-\lambda)$, a Berry–Esseen bound uniform in $\lambda$ shows each leaf length is approximately normal with mean $M\beta$ and spread $\sigma\sqrt M$. Since $\beta\to1$ as $\lambda\to1$ for any fixed $t$, the two heights produce leaf-length distributions whose centres differ by $o(\sigma\sqrt M)$, and explicit local lower bounds on the transition probabilities over windows of width $\sqrt M$ give a uniform overlap between $\mathcal L_1$ and $\mathcal L_2$. Lengths alone therefore carry asymptotically too little information about divergence time, in contrast with full sequences, from which TKF91 parameters and phylogeny are identifiable.

## Proof depends on

- [Berry–Esseen theorem](../../../../../Probability/central-limit-theorems/berry-esseen-theorem/berry-esseen-bound/berry-esseen.md)

## Sources

- Wai-Tong Louis Fan, Brandon Legried, Sebastien Roch, "Impossibility of consistent distance estimation from sequence lengths under the TKF91 model", arXiv:2005.11625 (2020), Definitions 1–2 (Section 2), Theorem 1 (Section 3), Lemmas 1–4 (Section 4), Remark 1, <https://doi.org/10.48550/arXiv.2005.11625>.
- J. L. Thorne, H. Kishino, J. Felsenstein, "An evolutionary model for maximum likelihood alignment of DNA sequences", *Journal of Molecular Evolution* 33 (1991) 114–124.
