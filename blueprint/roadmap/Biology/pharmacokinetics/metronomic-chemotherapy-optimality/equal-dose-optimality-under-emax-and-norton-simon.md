# Optimality of equal fractionated doses under Emax pharmacodynamics and the Norton–Simon hypothesis

**Model.** Tumour volume $L(t)$ grows by the Gompertz law and the cytotoxic effect follows the Norton–Simon hypothesis (kill proportional to the untreated growth rate):

$$L'(t)=\xi L(t)\log\Big(\frac{\theta}{L(t)}\Big)\big(1-\rho(t)\big),\qquad L(0)=L_0\in(0,\theta).$$

For $\rho\in L^\infty(0,T)$ the unique Lipschitz solution is

$$L(t)=\theta\exp\Big(\log(L_0/\theta)\,\exp\Big(-\xi\int_0^t\big(1-\rho(s)\big)\,ds\Big)\Big),$$

so $L(T)$ is decreasing in the cumulative effect $\int_0^T\rho$. The effect is the Emax response $\rho(t)=k_1c(t)/(k_2+c(t))$ to the drug concentration, which follows one-compartment bolus kinetics

$$c'(t)=-\lambda c(t)+\sum_{i=1}^N\sigma d_i\,\delta(t-t_i),\qquad c(0)=0,$$

with doses $d_i\in[d_{\min},d_{\max}]$ given at times $0\le t_1<\dots<t_N<T$. With $\tilde k_2=k_2/\sigma$ and $t_{N+1}=T$,

$$\int_0^T\rho(s)\,ds=\frac{k_1}{\lambda}\log\frac{(d_1+\tilde k_2)\prod_{i=2}^N\big(\sum_{j<i}d_je^{\lambda(t_j-t_i)}+d_i+\tilde k_2\big)}{\prod_{i=1}^N\big(\sum_{j\le i}d_je^{\lambda(t_j-t_{i+1})}+\tilde k_2\big)} .$$

When the drug clears between doses ($\lambda(t_{i+1}-t_i)$ large) the argument of the logarithm is approximately $\hat f_1(N,d)=\prod_{i=1}^N(1+d_i/\tilde k_2)$, independent of the administration times.

**Theorem (curative problem).** Maximize $\hat f_1(N,d)$ subject to a fixed total dose $\sum_id_i=D$ and $d_{\min}\le d_i\le d_{\max}$, assuming $[D/d_{\max},D/d_{\min}]\cap\mathbb N\neq\emptyset$. For each feasible $N$ the unique optimum is $d_i=D/N$ for all $i$, and over $N$ the optimum is

$$\hat N=\lfloor D/d_{\min}\rfloor,\qquad \hat d_i=D/\hat N .$$

**Theorem (palliative problem).** Minimize the total dose $\sum_id_i$ subject to $\hat f_1(N,d)\ge e^{\tilde T_R}$ (equivalent to a final-size bound $L(T)\le L_*$, with $\tilde T_R$ determined by $\xi,\theta,L_0,L_*,T,\lambda,k_1$). For each $N\in[N_{\min},N_{\max}-1]$, where $N_{\min}=\lceil\tilde T_R/\log(1+d_{\max}/\tilde k_2)\rceil$ and $N_{\max}=\lceil\tilde T_R/\log(1+d_{\min}/\tilde k_2)\rceil$, the unique optimum is

$$d_i=\tilde k_2\big(e^{\tilde T_R/N}-1\big),\qquad i=1,\dots,N,$$

and the global optimum uses $\hat N=N_{\max}-1$ doses of $d^*=\tilde k_2(e^{\tilde T_R/(N_{\max}-1)}-1)$ if $(N_{\max}-1)d^*\le N_{\max}d_{\min}$, and otherwise $\hat N=N_{\max}$ doses of $d_{\min}$.

Both problems are therefore solved by giving the largest admissible number of equal doses close to the minimal effective dose, which is the metronomic schedule.

## Expansion

The Gompertz–Norton–Simon equation linearizes under $\log\log(\theta/L)$, which turns minimizing $L(T)$ into maximizing $\int\rho$. Under fast clearance each bolus contributes $\frac{k_1}{\lambda}\log(1+d_i/\tilde k_2)$, a strictly concave function of the dose (the Emax saturation), so for a fixed budget the sum is maximized by equal doses (Jensen or AM–GM on the product), and more, smaller doses are better as long as each stays above $d_{\min}$. The palliative problem is the dual: the cheapest way to reach a fixed product $\prod(1+d_i/\tilde k_2)$ is again equal factors, and the trade-off over $N$ reduces to comparing the last two admissible values. Administration times are chosen afterwards so that the fast-clearance approximation holds.

## Sources

- Luis A. Fernández, Cecilia Pola, Judith Sáinz-Pardo, "A mathematical justification for metronomic chemotherapy in oncology", Mathematical Modelling of Natural Phenomena 17 (2022), 12, <https://doi.org/10.1051/mmnp/2022010>. Published version of arXiv:2110.07250, cited next; locators there refer to the arXiv version.
- Luis A. Fernández, Cecilia Pola, Judith Sáinz-Pardo, "A mathematical justification for metronomic chemotherapy in oncology", arXiv:2110.07250 (2021): Theorem 1, Proposition 1, Lemma 1, problems $(\hat P_1)$ and $(\hat P_2)$, Theorems 2–3 and Corollaries 1–2. <https://doi.org/10.48550/arXiv.2110.07250>
