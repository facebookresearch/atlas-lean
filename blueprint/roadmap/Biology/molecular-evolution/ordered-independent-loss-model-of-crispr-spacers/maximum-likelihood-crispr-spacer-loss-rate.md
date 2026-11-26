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

(b) Given $M=m\ge 2$ and $D=d$, the maximum likelihood estimator of $\rho$ maximizes

$$
(m-1)\log\frac{e^{-\rho T}}{2-e^{-\rho T}}+d\,\log\frac{1-e^{-\rho T}}{2-e^{-\rho T}},
$$

and is explicit:

$$
\rho^{*}=-\frac{\log p^{*}}{T},\qquad p^{*}=\left(1+\frac{d}{2(m-1)}\right)^{-1}.
$$

## Depends on

- [Distribution of shared-spacer positions in two CRISPR arrays](equal-spacer-gaps-in-two-crispr-arrays.md)

## Expansion

By the two-array distribution theorem, the gap pairs $(\Delta V_i,\Delta W_i)$, $i\ge 2$, are i.i.d. with $\mathbb P(a,b)=\binom{a+b}{a}\frac{p}{2-p}\big(\frac{1-p}{2-p}\big)^{a+b}$, $p=e^{-\rho T}$. The product over $i=2,\dots,m$ is $h\cdot\exp(c(\rho)\,t-d(\rho))$ with $h=\prod_i\binom{\Delta v_i+\Delta w_i}{\Delta v_i}$, $c(\rho)=\log\frac{1-p}{2-p}$ and $d(\rho)=-(m-1)\log\frac{p}{2-p}$, which gives (a). For (b), differentiate in $p$:

$$
\frac{d}{dp}\Big[(m-1)\log\tfrac{p}{2-p}+d\log\tfrac{1-p}{2-p}\Big]=\frac{2(m-1)(1-p)-p\,d}{p(1-p)(2-p)},
$$

whose unique zero in $(0,1)$ is $p^{*}=2(m-1)/(2(m-1)+d)$. The same estimator arises if one wrongly treats $V_M-V_1$ and $W_M-W_1$ as independent negative binomials, so the dependence between the two arrays does not change the point estimate for samples of size two.

## Sources

- Franz Baumdicker, Ariana M. I. Huebner and Peter Pfaffelhuber, "The independent loss model with ordered insertions for the evolution of CRISPR spacers", arXiv (2017): Definition 4.1 (statistics $M$ and $D$), Theorem 4 (sufficient statistic and explicit maximum likelihood estimator), and the remark following it on the independence assumption. <https://doi.org/10.48550/arXiv.1703.00220>
