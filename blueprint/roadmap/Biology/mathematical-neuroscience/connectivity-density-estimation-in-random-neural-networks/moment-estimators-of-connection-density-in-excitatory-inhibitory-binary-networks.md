# Moment estimators of connection density in excitatory-inhibitory binary networks

**Model.** Let $\theta_{ij}\sim\mathrm{Ber}(p)$, $1\le i,j\le N$, be i.i.d. (a directed Erdős–Rényi graph of synaptic connections). The neurons are split into excitatory and inhibitory sets $\mathcal P_+\sqcup\mathcal P_-=\{1,\dots,N\}$ with fractions $|\mathcal P_\pm|/N\to r_\pm\in(0,1)$, $r_++r_-=1$. Given $\theta$, the spike indicators $X_t=(X_{1,t},\dots,X_{N,t})\in\{0,1\}^N$ form a stationary Markov chain in which, given $X_{t-1}=x$, the $X_{i,t}$ are independent Bernoulli with

$$p_{\theta,i}(x)=\mu+(1-\lambda)\Big(\frac1N\sum_{j\in\mathcal P_+}\theta_{ij}x_j+\frac1N\sum_{j\in\mathcal P_-}\theta_{ij}(1-x_j)\Big),\qquad 0<\mu<\lambda<1 .$$

From one observed window $X_1,\dots,X_T$ ($\theta$ unobserved), with $Z_{i,t}=\sum_{s\le t}X_{i,s}$ and $\bar Z_t=N^{-1}\sum_iZ_{i,t}$, define the spatio-temporal mean, spatial variance and temporal variance

$$\hat m=\frac{\bar Z_T}{T},\qquad \hat v=\frac{(T+1)N}{T^3}\Big[\frac1N\sum_iZ_{i,T}^2-\frac{T}{T+1}\big(\bar Z_T+\bar Z_T^2\big)\Big],\qquad \hat w=2\mathcal W_{2\Delta}-\mathcal W_\Delta,$$

where $\mathcal W_\Delta=\frac NT\sum_{k=1}^{\lfloor T/\Delta\rfloor}\big(\bar Z_{k\Delta}-\bar Z_{(k-1)\Delta}-\Delta\hat m\big)^2$ and $1\le\Delta\le\lfloor T/2\rfloor$.

**Theorem.** There is $K=K(\lambda)$ such that for all $\varepsilon\in(0,1)$, $N\ge1$, $T\ge2$,

$$\mathbb P(|\hat m-m|\ge\varepsilon)\le\tfrac K\varepsilon\big(\tfrac1{\sqrt{TN}}+\tfrac1N\big),\quad \mathbb P(|\hat v-v|\ge\varepsilon)\le\tfrac K\varepsilon\big(\tfrac{\sqrt N}{T}+\tfrac1{\sqrt N}\big),\quad \mathbb P(|\hat w-w|\ge\varepsilon)\le\tfrac K\varepsilon\big(\tfrac1N+\tfrac{(1-\lambda)^\Delta}{\Delta}+\sqrt{\tfrac\Delta T}\big),$$

where, with $D=1-p(1-\lambda)(r_+-r_-)$,

$$m=\frac{\mu+(1-\lambda)pr_-}{D},\qquad v=(1-\lambda)^2p(1-p)\big((m-r_-)^2+r_+r_-\big),\qquad w=m(1-m)\frac{1+4(1-\lambda)^2p^2r_+r_-}{D^2}.$$

The map $(\mu,\lambda,p)\mapsto(m,v,w)$ has an explicit inverse branch $\Phi^{(-)}$ that recovers the parameters whenever $r_+\ge1/2$, or $\kappa(m,w)=(r_+-r_-)^2w/(m(1-m))\ge4r_+r_-$, so $\Phi^{(-)}(\hat m,\hat v,\hat w)$ estimates $(\mu,\lambda,p)$ with error probability at most $\frac K\varepsilon\big(\frac{\sqrt N}{T}+\frac1{\sqrt N}+\frac{(1-\lambda)^\Delta}{\Delta}+\sqrt{\Delta/T}\big)$; choosing $\Delta\asymp\log T$ gives the rate $N^{-1/2}+N^{1/2}/T+(\log T/T)^{1/2}$.

## Expansion

In the mean-field limit each neuron's firing probability is driven by the population activity, so $m$ solves the linear fixed point $m=\mu+(1-\lambda)p(r_+m+r_-(1-m))$. The spread of individual firing rates across neurons comes from the randomness of each neuron's in-degree, which is $p(1-p)$-sized and gives the spatial variance $v$; the fluctuations of the population average over time blocks give $w$, inflated by the network feedback factor $D^{-2}$. Correlations between $X_{i,t}$ and $X_{j,s}$ for fixed $\theta$ are controlled by a backward regeneration (perfect simulation) construction in which each spike is traced back through coalescing random walks that die at rate $\lambda$; two walkers meet with probability $O((1-\lambda)^{|t-s|}/N)$, which makes all three statistics concentrate. Knowing the excitatory fraction (about $0.7$–$0.8$ in mammalian cortex) then lets the connection density be read off from spike trains alone.

## Sources

- Julien Chevallier, Eva Löcherbach and Guilherme Ost, "Inferring the dependence graph density of binary graphical models in high dimension", The Annals of Statistics 54 (2026), 861–881, <https://doi.org/10.1214/25-aos2592>; numbering as in arXiv:2406.07066: Section 2 (model, estimators, Theorem 2.1, Proposition 2.2, Corollary 2.4) and Proposition 3.5.
