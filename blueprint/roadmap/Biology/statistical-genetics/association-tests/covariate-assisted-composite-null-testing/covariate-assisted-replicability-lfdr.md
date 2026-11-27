# Covariate-assisted local FDR for replicability

**Model.** For features $i=1,\dots,m$ observe p-values $p_{1i},p_{2i}$ from two primary studies and an auxiliary covariate $x_i\in(0,1)$ (a p-value from a related study). Hidden states $\theta_{1i},\theta_{2i},\zeta_i\in\{0,1\}$ mark non-null effects, with joint state $s_i=(\theta_{1i},\theta_{2i},\zeta_i)$ and prior $P(s_i=(k,l,r))=\xi_{klr}$ on the eight states $S=\{0,1\}^3$. Given the states, the three p-values are independent with

$$p_{1i}\mid\theta_{1i}\sim(1-\theta_{1i})f_{10}+\theta_{1i}f_{11},\quad p_{2i}\mid\theta_{2i}\sim(1-\theta_{2i})f_{20}+\theta_{2i}f_{21},\quad x_i\mid\zeta_i\sim(1-\zeta_i)f_{30}+\zeta_if_{31},$$

where $f_{10}=f_{20}=f_{30}$ is the uniform density and the non-null densities lie in $\mathcal G=\{f:\text{non-increasing density on }(0,1)\}$. The auxiliary state may disagree with the primary states.

**Composite null.** $H_{0i}:\ s_i\in\mathcal H=S\setminus\{(1,1,0),(1,1,1)\}$, i.e. not non-null in both primary studies.

**Local FDR.**

$$\mathrm{Lfdr}_i=1-P(\theta_{1i}=\theta_{2i}=1\mid p_{1i},p_{2i},x_i)=\frac{\sum_{(k,l,r)\in\mathcal H}\xi_{klr}f_{1k}(p_{1i})f_{2l}(p_{2i})f_{3r}(x_i)}{\sum_{(k,l,r)\in S}\xi_{klr}f_{1k}(p_{1i})f_{2l}(p_{2i})f_{3r}(x_i)},$$

which is non-decreasing in $p_{1i}$ and in $p_{2i}$ when $f_{11},f_{21}\in\mathcal G$. It is also non-decreasing in $x_i$ when $f_{31}\in\mathcal G$ and the auxiliary signal goes with the replicable state, in the sense that $\xi_{kl1}\xi_{110}\le\xi_{kl0}\xi_{111}$ for every $(k,l)\ne(1,1)$; without this condition monotonicity in $x_i$ can fail.

*Monotonicity.* With $t=f_{31}(x_i)$, $\mathrm{Lfdr}_i/(1-\mathrm{Lfdr}_i)=\sum_{(k,l)\ne(1,1)}\frac{f_{1k}(p_{1i})f_{2l}(p_{2i})}{f_{11}(p_{1i})f_{21}(p_{2i})}\cdot\frac{\xi_{kl0}+\xi_{kl1}t}{\xi_{110}+\xi_{111}t}$. Each first factor is $1$ or a product of the non-decreasing ratios $1/f_{11}(p_{1i})$ and $1/f_{21}(p_{2i})$. The second factor is non-increasing in $t$, hence non-decreasing in $x_i$, exactly when $\xi_{kl1}\xi_{110}\le\xi_{kl0}\xi_{111}$. For instance, with $\xi_{000}=0.3$, $\xi_{001}=0.4$, $\xi_{110}=0.29$, $\xi_{111}=0.01$, the other weights $0$, $f_{11}=f_{21}=f_{31}=2(1-u)$ and $p_{1i}=p_{2i}=0.05$, $\mathrm{Lfdr}_i$ is $0.494$ at $x_i=0.01$ and $0.227$ at $x_i=0.99$. The source states monotonicity in all three arguments without this restriction.

**Covariate as a feature-specific prior.** Conditionally on $x_i$,

$$f(p_{1i},p_{2i}\mid x_i)=\eta_{00}f_{10}f_{20}+\eta_{01}f_{10}f_{21}+\eta_{10}f_{11}f_{20}+\eta_{11}f_{11}f_{21},\qquad \eta_{kl}=\frac{\xi_{kl0}f_{30}(x_i)+\xi_{kl1}f_{31}(x_i)}{\sum_{k',l'}\xi_{k'l'0}f_{30}(x_i)+\sum_{k',l'}\xi_{k'l'1}f_{31}(x_i)},$$

so the four-group replicability mixture acquires prior weights $\eta_{kl}$ that vary with the covariate; the features are no longer exchangeable a priori.

**Step-up rule.** With estimated $\widehat{\mathrm{Lfdr}}_i$ ordered as $\widehat{\mathrm{Lfdr}}_{(1)}\le\dots\le\widehat{\mathrm{Lfdr}}_{(m)}$, reject $H_{(1)},\dots,H_{(\hat k)}$ for $\hat k=\max\{i:\ \tfrac1i\sum_{j\le i}\widehat{\mathrm{Lfdr}}_{(j)}\le\alpha\}$; equivalently threshold at $\hat\lambda=\sup\{\lambda:\sum_i\widehat{\mathrm{Lfdr}}_i\mathbf 1\{\widehat{\mathrm{Lfdr}}_i\le\lambda\}/(\sum_i\mathbf 1\{\widehat{\mathrm{Lfdr}}_i\le\lambda\}\vee1)\le\alpha\}$.

**Several covariates.** Auxiliary p-values $p_{ki}$ ($k=1,\dots,n$) are merged by the Cauchy combination $T_i=\sum_kw_k\tan\{(0.5-p_{ki})\pi\}$, $w_k\ge0$, $\sum_kw_k=1$, and $x_i=0.5-\arctan(T_i)/\pi$; under the null $T_i$ is standard Cauchy for independent inputs and approximately so under dependence, so $x_i$ is again approximately uniform.

## Depends on

- [Local false discovery rate](../../../../Probability/hypothesis-testing/two-groups-model-and-local-false-discovery-rates/local-fdr.md)

## Expansion

The conditional mixture follows from Bayes' rule and conditional independence: integrating out $\zeta_i$ against $f(x_i\mid\zeta_i)$ turns the joint prior $\xi$ into covariate-dependent weights on the four primary states. A small auxiliary p-value raises the weight of states with $\zeta_i=1$ and, through correlation of the hidden states, of the replicable state $(1,1)$, lowering $\mathrm{Lfdr}_i$; an uninformative covariate leaves the weights at their marginal values. The step-up rule is the usual running-mean estimate of the false discovery proportion among the features with the smallest Lfdr.

## Sources

- Y. Li, Y. Li, H. Ma, Z. Yue, X. Zhang, "Coconut: covariate-assisted composite null hypothesis testing with applications to replicability analysis of high-throughput experimental data", *BMC Bioinformatics* 26 (2025), Methods: oracle procedure (Equations (1)–(2)), motivation to incorporate auxiliary information (Equation (3) and the derivation of $\eta_{kl}$), optimal FDR control procedure, and combination of multiple auxiliary covariates, <https://doi.org/10.1186/s12859-025-06163-8>, PMCID PMC12210505.
