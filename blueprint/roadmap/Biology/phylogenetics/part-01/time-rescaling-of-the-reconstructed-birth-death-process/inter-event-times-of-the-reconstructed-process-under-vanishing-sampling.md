# Inter-event times of the reconstructed process under vanishing sampling

**Setting.** Let $X_\psi$ be the reversed reconstructed process of a supercritical birth–death process conditioned on $n$ sampled tips. Measure time in units $\delta=(\lambda-\mu)\tau$ and write $\lambda'=\lambda/(\lambda-\mu)$. Let $T_0=0<T_1<\dots<T_n$ be the event times, with $T_n$ the time to origin, and let $W_k=T_{k+1}-T_k$. The regime of interest is a finite sample taken from a very large population, $\psi\to0$ with $\lambda'$ fixed.

**Theorem.**

1. *(Exact law for every $\psi\in(0,1]$.)* For $k\in\{0,\dots,n-1\}$,

$$f^{\psi}_{W_k}(w)=\frac{n-k}{n+1}e^{-(n-k)w}\Big[(n+1)\,{}_2F_1\big(n-k+1,n-k+1;n+1;z\big)-(1-\psi\lambda')(n-k+1)\,{}_2F_1\big(n-k+1,n-k+2;n+2;z\big)\Big],$$

where $z=(1-\psi\lambda')(1-e^{-w})$.
2. *(Limit $\psi\to0$.)* For $k\in\{1,\dots,n-1\}$,

$$f^{0}_{W_k}(w)=\frac{k(n-k)}{n+1}e^{-(n-k)w}\,{}_2F_1\big(n-k+1,n-k+1;n+2;1-e^{-w}\big).$$

3. *(Near-exponentiality of each marginal.)* For $k\in\{1,\dots,n-1\}$ let $F^{0}_{W_k}$ be the distribution function of the limiting density $f^0_{W_k}$ of item 2, and $\widetilde F_{W_k}$ the exponential distribution function with rate $k(n-k)/n$. Then, for every $k\in\{1,\dots,n-1\}$,

$$\sup_w\big|F^{0}_{W_k}(w)-\widetilde F_{W_k}(w)\big|<\frac1n .$$

4. *(Means.)* As $\psi\to0$,

$$\mathbb E(T_n)=\log\frac{1}{\psi\lambda'}+\sum_{j=1}^{n-1}\frac1j+O(\psi),\qquad \mathbb E(W_k)=\frac{n}{k(n-k)}+O(\psi)\quad(1\le k\le n-1).$$

So for small sampling fractions each individual waiting time $W_k$, $1\le k\le n-1$, has a limiting marginal law within Kolmogorov–Smirnov distance $1/n$ of an exponential law with rate $k(n-k)/n$. The bound concerns the marginals one at a time; it says nothing about the joint law of $(W_1,\dots,W_{n-1})$, which are not independent, so it does not make the genealogy a Markov death process with independent exponential waits. Its total depth is $\log(1/(\psi\lambda'))$ plus the depth of a Yule tree with $n$ tips.

## Expansion

All four items come from the time-rescaling identity $X_\psi(\tau)=Y(\rho_\psi(\tau))$ with a unit-rate pure-death process $Y$. The event times of $Y$ have explicit order-statistic densities. With $U_k$ the partial sums of the independent holding times of $Y$, $W_k=\rho_\psi^{-1}(U_{k+1})-\rho_\psi^{-1}(U_k)$ is a difference of two rescaled event times (not the rescaled holding time $\rho_\psi^{-1}(U_{k+1}-U_k)$); integrating the joint density of $(U_k,U_{k+1})$ over the first gives a hypergeometric integral, which is item 1. As $\psi\to0$ the map $\rho_\psi$ becomes an almost-linear shift by $\log(1/(\psi\lambda'))$ on the bulk of the tree, which gives item 2 and the origin-time asymptotics. The Kolmogorov–Smirnov bound comes from comparing the hypergeometric distribution function with an exponential of the same mean.

These are Theorem 1, Corollaries 1–2 and Propositions 2–4 (Sections 4.3–4.5) of the source.

## Depends on

- [Reversed reconstructed process as a time-rescaled Yule process](reversed-reconstructed-process-as-a-time-rescaled-yule-process.md)

## Sources

- A. Ignatieva, J. Hein, P. A. Jenkins, "A characterisation of the reconstructed birth-death process through time rescaling", arXiv:1912.04861 (2019). <https://doi.org/10.48550/arXiv.1912.04861>
- Published version: A. Ignatieva, J. Hein, P. A. Jenkins, "A characterisation of the reconstructed birth–death process through time rescaling", Theoretical Population Biology 134 (2020), 61–76, <https://doi.org/10.1016/j.tpb.2020.05.001>.
