# Big loop versus unbound strand in the localized generalized Poland–Scheraga model

**Setting.** Consider the generalized Poland–Scheraga model of two DNA strands of lengths $N$ and $M$, with loop weight $K(n)=L(n)n^{-(2+\alpha)}$ ($\alpha>0$), binding energy $h>0$, and critical aspect ratio $\gamma_c(h)$. In the *free* version the terminal portions of both strands may stay unbound. An unbound end of length $j$ has weight $K_f(j)=\overline L(j)\,j^{-\overline\alpha}$, with $K_f(0)=1$, $\overline\alpha\in\mathbb R$ and $\overline L$ slowly varying:

$$Z^f_{N,M,h}=\sum_{i=0}^N\sum_{j=0}^M K_f(i)K_f(j)\,Z^c_{N-i,M-j,h}.$$

Write $M=\gamma_c(h)N+t_N$ with $t_N$ in the big-jump regime: $t_N/a^{(2)}_N\to\infty$, plus $t_N^2/(N\sigma(t_N))\ge C_0\log N$ when $\alpha\ge1$. Two kinds of configurations compete:

- the *Big Loop* event $E_{\rm BL}$: one loop of size $t_N+O(a^+_N)$, all other loops smaller than $m^+_N$, and both unbound ends at most $u_N$;
- the *Unbound Strand* event $E_{\rm US}$: all loops smaller than $m^+_N$, the shorter strand's unbound end at most $u_N$, and the longer strand's unbound end of length $t_N+O(\tilde a^+_N)$.

Here $u_N\to\infty$ and $t_N\gg a^+_N,\tilde a^+_N\gg a^{(2)}_N$, $t_N\gg m^+_N\gg m^{(2)}_N$.

**Theorem.** Under the free measure $\mathbf P^f_{N,M,h}$:

1. Unless $\overline\alpha=1$ and $\sum_jK_f(j)=\infty$, $\mathbf P^f_{N,M,h}(E_{\rm BL}\cup E_{\rm US})\to1$.
2. If $\overline\alpha<1$, so that $\sum_jK_f(j)=\infty$, then $\mathbf P^f_{N,M,h}(E_{\rm US})\to1$.
3. If $\sum_jK_f(j)<\infty$, then

$$\mathbf P^f_{N,M,h}(E_{\rm US})\sim\frac1{1+Q_N},\qquad \mathbf P^f_{N,M,h}(E_{\rm BL})\sim\frac{Q_N}{1+Q_N},$$

with

$$Q_N=c_h\,N\,t_N^{-(2+\alpha)+\overline\alpha}\,\frac{L(t_N)}{\overline L(t_N)},\qquad c_h=\frac{e^h\sum_{j\ge0}K_f(j)}{\hat\mu_1\,(e^{\mathrm N(h)}-1)} .$$

In particular, if $t_N\sim cN$ then the unbound strand wins when $\overline\alpha<\alpha+1$ and the big loop wins when $\overline\alpha>\alpha+1$. At $\overline\alpha=\alpha+1$ the ratio of the slowly varying functions decides.

## Expansion

The free partition function splits into two leading contributions. One is the constrained mass with short free ends, $\overline K\,\frac{N}{\hat\mu_1^2}\bigl(\sum_iK_f(i)e^{-i\mathrm N(h)}\bigr)\mathbf P(\hat\tau^{(2)}_1=\lceil t_N\rceil)$, where $\overline K=\sum_{j\ge1}K_f(j)$ when finite and $0$ otherwise. The other is $\frac1{\hat\mu_1}\bigl(\sum_iK_f(i)e^{-i\mathrm N(h)}\bigr)K_f(t_N)$, where the whole mismatch goes into one free end. Comparing the polynomial tails $N\,t_N^{-(2+\alpha)}$ (a big loop placed anywhere along the chain) and $t_N^{-\overline\alpha}$ (one long free end) gives $Q_N$. Matching lower bounds on each event turn this bookkeeping into the dichotomy for trajectories. The marginal case $\overline\alpha=1$ with $\sum_jK_f(j)=\infty$ is excluded, and there a big loop and a long unbound end can coexist.

## Depends on

- [Big-jump asymptotics of the constrained generalized Poland–Scheraga partition function](big-jump-asymptotics-of-the-constrained-generalized-poland-scheraga-partition-function.md)

## Sources

- Quentin Berger, Giambattista Giacomin, Maha Khatib, "DNA melting structures in the generalized Poland-Scheraga model", arXiv:1703.10343 (2017), Theorem 1.1 and Theorem 2.2 (Sections 1–2), <https://doi.org/10.48550/arXiv.1703.10343>.
