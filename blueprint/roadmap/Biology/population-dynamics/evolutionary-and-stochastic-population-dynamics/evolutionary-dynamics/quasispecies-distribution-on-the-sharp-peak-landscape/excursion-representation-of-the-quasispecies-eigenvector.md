# Excursion representation of the quasispecies eigenvector

**Setting.** Let $E$ be a finite genotype space, $f:E\to(0,\infty)$ a fitness function and $M$ a mutation matrix with all entries positive (hypothesis (H)). Stationary solutions of Eigen's quasispecies system are probability vectors $x$ with

$$
x(u)\sum_{v\in E}x(v)f(v)=\sum_{v\in E}x(v)f(v)M(v,u)\qquad(u\in E).
$$

Under (H) the Perron–Frobenius theorem applied to $fM=(f(u)M(u,v))$ gives a unique such solution: the normalized left Perron eigenvector, with mean fitness equal to the Perron eigenvalue $\lambda$.

**Theorem.** Let $(S_n)_{n\ge0}$ be the Markov chain on $E$ with transition matrix $M$, $E_w$ its law started at $w$, and $\tau_w=\inf\{n\ge1:S_n=w\}$. For any $w\in E$ the unique solution is

$$
x(u)=\frac{E_w\Bigl(\sum_{n=0}^{\tau_w-1}\mathbf 1_{\{S_n=u\}}\,\lambda^{-n}\prod_{k=0}^{n-1}f(S_k)\Bigr)}{E_w\Bigl(\sum_{n=0}^{\tau_w-1}\lambda^{-n}\prod_{k=0}^{n-1}f(S_k)\Bigr)} ,\qquad u\in E .
$$

Taking $w=u$ gives

$$
x(u)=\frac{1}{E_u\Bigl(\sum_{n=0}^{\tau_u-1}\lambda^{-n}\prod_{k=0}^{n-1}f(S_k)\Bigr)} .
$$

## Expansion

This is the fitness-weighted analogue of the cycle formula for the stationary law of a Markov chain (the case $f\equiv1$, $\lambda=1$, where $x(u)=1/E_u\tau_u$). Following a lineage backwards, each generation multiplies the weight by the fitness of the current genotype and divides by the mean fitness $\lambda$; the eigenvector is the expected weighted occupation of $u$ during one excursion from $w$. Verification is direct: plugging the formula into the system and splitting the excursion at its first step reproduces the eigen-equation, and the denominator normalizes. The representation explains the combinatorial closed forms on the sharp peak landscape as generating functions of weighted excursions of the mutation chain away from the master sequence.

## Sources

- Raphaël Cerf, Joseba Dalmau, *The quasispecies distribution*, arXiv (2016). Sections 2–3 (quasispecies model, Perron–Frobenius) and Section 12 (the Perron–Frobenius eigenvector: theorem and corollary). <https://doi.org/10.48550/arXiv.1609.05738> Published version: R. Cerf and J. Dalmau, The Quasispecies Equation and Classical Population Models, Springer (2022), <https://doi.org/10.1007/978-3-031-08663-2>.
