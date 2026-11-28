# Extremal gaps between the Fair Proportion and Equal Splits indices

**Setting.** Let $T$ be a rooted binary phylogenetic tree with leaf set $[n]$, root $\rho$ and edge lengths $l(e)>0$. For a leaf $i$ let $P(T;\rho,i)$ be the root-to-$i$ path. The two diversity indices apportioning the total phylogenetic diversity $\sum_e l(e)$ among species are

$$FP_T(i)=\sum_{e\in P(T;\rho,i)}\frac{l(e)}{n(e)},\qquad ES_T(i)=\sum_{e\in P(T;\rho,i)}\frac{l(e)}{\Pi(e,i)},$$

where $n(e)$ is the number of leaves below $e$ (Fair Proportion shares each edge equally among its descendants) and $\Pi(e,i)=2^{m}$ with $m$ the number of edges between $e$ and leaf $i$ (Equal Splits halves each edge's share at every branching point). The molecular clock condition (MC) requires all root-to-leaf path lengths to be equal. Define $\Delta_n(FP/ES)$ and $\Delta_n(ES/FP)$ as the suprema of $FP_T(i)/ES_T(i)$ and $ES_T(i)/FP_T(i)$ over binary trees with $n$ leaves, leaves $i$ and positive edge lengths; and $\Delta_n(FP-ES;\cdot)$, $\Delta_n(ES-FP;\cdot)$ as the suprema of the differences when either the longest edge $l_{\max}$ or the total length $L$ is fixed.

**Theorem.**

1. For $n\ge3$,

$$\Delta_n(FP/ES)=\frac{2^{n-2}}{n-1},\qquad \Delta_n(ES/FP)=\frac{n-1}{2},$$

and these values remain the same under (MC).

2. For $n\ge4$, $\Delta_n(FP-ES;l_{\max})=l_{\max}(\ln n+\gamma-2)+o(1)$, with $\gamma$ the Euler–Mascheroni constant, while $\Delta_n(ES-FP;l_{\max})<l_{\max}$ and $\sup_n\Delta_n(ES-FP;l_{\max})=l_{\max}$. Under (MC), $\Delta_n(FP-ES;l_{\max})<\frac{2}{\ln2}\,l_{\max}$.

3. In terms of total length, $\Delta_n(FP-ES;L)=\lambda_nL$ with $\lambda_2=\lambda_3=0$, $\lambda_4=\tfrac1{12}$, $\lambda_5=\tfrac18$ and $\lambda_n=\tfrac{11}{80}$ for $n\ge6$; and $\Delta_n(ES-FP;L)=\big(\tfrac12-\tfrac1{n-1}\big)L$ for $n\ge3$. Under (MC) the same formulas hold with $L$ replaced by $L/2$.

So the two indices can disagree by an exponential factor in ratio, but in absolute terms FP exceeds ES by at most a logarithmic multiple of the longest edge and by at most $11/80$ of the total tree length.

## Expansion

Both indices are linear in the edge lengths, so ratios are extremized by concentrating length on one edge of the path to $i$; the extreme coefficients $1/n(e)$ versus $1/\Pi(e,i)$ occur on a caterpillar, where an edge $m$ steps above a cherry leaf has $n(e)=m+1$ but $\Pi(e,i)=2^{m}$ for that leaf, or the reverse for the leaf at the far end. For differences with bounded longest edge, setting all edges on the path to $l_{\max}$ in a caterpillar gives $\sum_m(1/(m+1)-2^{-m})$, a harmonic sum minus a geometric one, which produces $\ln n+\gamma-2$. With total length fixed the problem becomes maximizing a single coefficient difference $1/n(e)-1/\Pi(e,i)$, and the best configurations stabilize for $n\ge6$, giving $11/80$.

## Sources

- Kristina Wicke, Mike Steel, "Combinatorial properties of phylogenetic diversity indices", arXiv:1902.02463 (2019): Section 1.2 (definitions of FP and ES, molecular clock condition), Section 2 (theorems on maximal ratios, maximal differences in terms of $l_{\max}$ and in terms of $L$). <https://doi.org/10.48550/arXiv.1902.02463> Published version: Journal of Mathematical Biology 80 (2019) 687–715, <https://doi.org/10.1007/s00285-019-01438-0>.
