# Big-jump asymptotics of the constrained generalized Poland–Scheraga partition function

**Model.** The generalized Poland–Scheraga (gPS) model describes two DNA strands of lengths $N$ and $M$. A configuration is a bivariate renewal $\tau=\{\tau_n\}\subset\mathbb N_0^2$ with $\tau_0=(0,0)$ and i.i.d. increments in $\mathbb N^2$ with law $\mathbf P(\tau_1=(n,m))=K(n+m)$. Here $K(n)=L(n)\,n^{-(2+\alpha)}$ with $\alpha>0$, $L$ slowly varying, and $\sum_{n,m}K(n+m)=1$. An increment $(1,1)$ is a bound base pair, and any other increment $(i,j)$ is a loop with $i$ bases on one strand and $j$ on the other. Each contact gets weight $e^h$ with binding energy $h\in\mathbb R$. The constrained partition function sums over configurations that bind the last bases, $(N,M)\in\tau$.

For $h>0$ let $\mathrm N(h)>0$ solve $\sum_{n,m\ge1}K(n+m)e^{-n\mathrm N(h)}=e^{-h}$. Define the tilted inter-arrival law $\hat K_h(n,m)=K(n+m)e^{h-n\mathrm N(h)}$ and its renewal $\hat\tau=(\hat\tau^{(1)},\hat\tau^{(2)})$, with means $\hat\mu_1,\hat\mu_2$ and $\gamma_c(h)=\hat\mu_2/\hat\mu_1$. Then

$$Z^c_{N,M,h}=e^{N\mathrm N(h)}\,\mathbf P\bigl((N,M)\in\hat\tau\bigr).$$

The first marginal of $\hat K_h$ has exponential tails, while the second has a power tail, $\mathbf P(\hat\tau^{(2)}_1=m)\sim\frac{e^h}{e^{\mathrm N(h)}-1}L(m)m^{-(2+\alpha)}$. Let $a^{(2)}_N$ be the stable scaling sequence of $\hat\tau^{(2)}_N$, and $m^{(2)}_N$ the order of the largest of $N$ second-coordinate increments.

**Theorem.** Fix $h>0$ and write $M=\gamma_c(h)N+t_N$, where the strand mismatch beyond the typical direction satisfies $t_N/a^{(2)}_N\to\infty$. If $\alpha\ge1$, assume also $t_N^2/(N\sigma(t_N))\ge C_0\log N$ for a suitable constant $C_0$, where $\sigma(n)=\mathbf E[(\hat\tau^{(2)}_1)^2\mathbf 1\{\hat\tau^{(2)}_1\le n\}]$. Then:

1. (Sharp target probability.)

$$\mathbf P\bigl((N,M)\in\hat\tau\bigr)\ \sim\ \frac{N}{\hat\mu_1^2}\,\mathbf P\bigl(\hat\tau^{(2)}_1=\lceil t_N\rceil\bigr),\qquad N\to\infty .$$

2. (Big loop under the constrained measure.) Under $\mathbf P^c_{N,M,h}=\mathbf P(\cdot\mid(N,M)\in\hat\tau)$, with probability tending to $1$ the configuration has exactly one loop of size $t_N+O(a^+_N)$, all other loops are smaller than $m^+_N$, and nothing is left unbound. Here $a^+_N$ and $m^+_N$ are any sequences with $t_N\gg a^+_N\gg a^{(2)}_N$ and $t_N\gg m^+_N\gg m^{(2)}_N$.

In this non-Cramér part of the localized phase, the excess length of the longer strand condenses into one macroscopic loop, while the rest of the chain stays tightly bound.

## Expansion

The event $(N,M)\in\hat\tau$ needs about $N/\hat\mu_1$ renewal steps. Their second coordinates then overshoot the typical value $\gamma_cN$ by $t_N$. Because $t_N$ is much larger than the stable fluctuation scale $a^{(2)}_N$, the cheapest way to produce this deviation is a single big jump in one increment (the big-jump domain of subexponential random walks). There are $N/\hat\mu_1$ places for the jump, and the local constraint on the first coordinate contributes another factor $1/\hat\mu_1$. The extra $\log N$ condition for $\alpha\ge1$ rules out the competing strategy of many moderate jumps when the second moment is finite or barely infinite. The matching lower bound, restricted to one big loop and small other loops, gives the trajectory statement.

## Sources

- Quentin Berger, Giambattista Giacomin, Maha Khatib, "DNA melting structures in the generalized Poland-Scheraga model", arXiv:1703.10343 (2017), Section 1 (model, tilted renewal and marginals, big-jump hypotheses), Theorem 2.1 and Theorem 2.3, <https://doi.org/10.48550/arXiv.1703.10343>.
