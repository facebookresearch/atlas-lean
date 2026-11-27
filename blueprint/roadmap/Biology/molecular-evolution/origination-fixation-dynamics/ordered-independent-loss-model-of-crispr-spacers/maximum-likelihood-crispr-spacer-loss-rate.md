# Maximum likelihood estimator of the CRISPR spacer loss rate from two arrays

**Setting.** Under the ordered independent loss model (spacers inserted at the leader end at rate $\theta$, each present spacer deleted independently at rate $\rho$, equilibrium i.i.d. uniform labels at the root), consider two arrays $S_1,S_2$ at leaves whose most recent common ancestor lies at known time $T>0$ in the past. Let $V_i,W_i$ be the positions in $S_1$ and $S_2$ of the $i$-th spacer shared by both arrays, and define

$$
M:=|S_1\cap S_2|,\qquad D:=\sum_{i=2}^{M}\big[(V_i-V_{i-1})+(W_i-W_{i-1})\big]=(V_M-V_1)+(W_M-W_1).
$$

**Statement.**

(a) For $m\ge 2$, the joint law of the gaps $\Delta V_i=V_i-V_{i-1}$, $\Delta W_i=W_i-W_{i-1}$, $i=2,\dots,m$, depends only on $\rho$ (not on $\theta$) and forms a one-parameter exponential family with sufficient statistic

$$
t=\sum_{i=2}^{m}(\Delta v_i+\Delta w_i)=(v_m-v_1)+(w_m-w_1).
$$

(b) Given $M=m\ge 2$ and $D=d$ (so $d\ge 2(m-1)$, since each gap is at least $1$), the maximum likelihood estimator of $\rho$ maximizes

$$
(m-1)\log\frac{e^{-\rho T}}{2-e^{-\rho T}}+\big(d-2(m-1)\big)\log\frac{1-e^{-\rho T}}{2-e^{-\rho T}},
$$

and is explicit:

$$
\rho^{*}=-\frac{\log p^{*}}{T}=\frac1T\log\frac{d}{2(m-1)},\qquad p^{*}=\frac{2(m-1)}{d}.
$$

In particular $\rho^*=0$ when all $m$ shared spacers are consecutive in both arrays ($d=2(m-1)$, no one-sided loss).

## Depends on

- [Distribution of shared-spacer positions in two CRISPR arrays under the ordered independent loss model](equal-spacer-gaps-in-two-crispr-arrays.md)

## Proof depends on

- [Discrete factorization, sufficiency](../../../../Probability/statistical-estimation/sufficient-statistics-and-the-factorization-theo/is-sufficient-pmf-of-factorization.md)

## Expansion

By the two-array distribution theorem, the shifted gap pairs $(\Delta V_i-1,\Delta W_i-1)$, $i\ge 2$, are i.i.d. with $\mathbb P(a,b)=\binom{a+b}{a}\frac{p}{2-p}\big(\frac{1-p}{2-p}\big)^{a+b}$, $p=e^{-\rho T}$. With $t'=t-2(m-1)$, the product over $i=2,\dots,m$ is $h\cdot\exp(c(\rho)\,t'-d(\rho))$ with $h=\prod_i\binom{\Delta v_i+\Delta w_i-2}{\Delta v_i-1}$, $c(\rho)=\log\frac{1-p}{2-p}$ and $d(\rho)=-(m-1)\log\frac{p}{2-p}$; since $t'$ is an affine function of $t$, this gives (a). For (b), with $k=d-2(m-1)$, differentiate in $p$:

$$
\frac{d}{dp}\Big[(m-1)\log\tfrac{p}{2-p}+k\log\tfrac{1-p}{2-p}\Big]=\frac{2(m-1)(1-p)-p\,k}{p(1-p)(2-p)},
$$

whose unique zero in $(0,1]$ is $p^{*}=2(m-1)/(2(m-1)+k)=2(m-1)/d$. The same estimator arises if one wrongly treats $V_M-V_1-(m-1)$ and $W_M-W_1-(m-1)$ as independent negative binomials with parameters $m-1$ and $p$, so the dependence between the two arrays does not change the point estimate for samples of size two.

## Sources

- Franz Baumdicker, Ariana M. I. Huebner and Peter Pfaffelhuber, *The independent loss model with ordered insertions for the evolution of CRISPR spacers*, Theor. Popul. Biol. 119 (2018), 72–82. <https://doi.org/10.1016/j.tpb.2017.11.001> Definition 4.1 (statistics $M$ and $D$), Theorem 4 (sufficient statistic and maximum likelihood estimator) and Remark 4.2 (the independence assumption). Locators use the numbering of the preprint arXiv:1703.00220. The estimator there inherits the missing shift by one in its Theorem 1; the version here subtracts the $2(m-1)$ shared-spacer steps from $D$.
