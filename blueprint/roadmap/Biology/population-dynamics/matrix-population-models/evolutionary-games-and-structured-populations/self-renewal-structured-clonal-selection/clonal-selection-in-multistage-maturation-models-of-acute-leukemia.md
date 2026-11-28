# Clonal selection in multistage maturation models of acute leukemia

**Model.** Leukemic clones are labelled by a trait $x\in[0,1]$. Cells pass through $M\ge3$ maturation compartments with densities $n_{i\varepsilon}(t,x)$: stem cells ($i=1$), progenitors ($2\le i\le M-1$) and mature cells/blasts ($i=M$), with feedback through the mature mass $\rho_{M\varepsilon}(t)=\int_0^1n_{M\varepsilon}\,dx$. On the slow time scale $t/\varepsilon$,

$$
\begin{aligned}
\varepsilon\,\partial_tn_{1\varepsilon}&=P_1(\rho_{M\varepsilon},x)\,n_{1\varepsilon},\\
\varepsilon\,\partial_tn_{i\varepsilon}&=Q_{i-1}(\rho_{M\varepsilon},x)\,n_{i-1,\varepsilon}+P_i(\rho_{M\varepsilon},x)\,n_{i\varepsilon},\quad 2\le i\le M-1,\\
\varepsilon\,\partial_tn_{M\varepsilon}&=Q_{M-1}(\rho_{M\varepsilon},x)\,n_{M-1,\varepsilon}-d\,n_{M\varepsilon},
\end{aligned}
$$

where $P_i(\rho,x)=\big(\frac{2a_i(x)}{1+K\rho}-1\big)p_i(x)$ and $Q_i(\rho,x)=2\big(1-\frac{a_i(x)}{1+K\rho}\big)p_i(x)$, with self-renewal fractions $a_i$ and proliferation rates $p_i$.

**Assumptions.** $a_i,p_i\in W^{1,\infty}([0,1])$, $a_i:[0,1]\to(\tfrac12,1)$, $p_i:[0,1]\to(0,1)$, and stem cells self-renew most, $\tfrac12<a_i(x)<a_1(x)<1$ for $i=2,\dots,M-1$; initial data are continuous with $0<n_i^0<\infty$ on $[0,1]$.

**Theorem.** As $\varepsilon\to0$, up to subsequences, $n_{i\varepsilon}\rightharpoonup n_i$ weakly-$*$ in $L^\infty((0,T),\mathcal M^1([0,1]))$, and $R_{i\varepsilon}\to R_i(t,x)=\int_0^tP_i(\rho_M(s),x)\,ds$ uniformly, with

$$
\max_{x\in[0,1]}R_1(t,x)=0,\qquad \max_{x\in[0,1]}R_i(t,x)<0\ \ (i=2,\dots,M-1),\qquad \operatorname{supp}n_i(t,\cdot)=\arg\max_{x\in[0,1]}a_1(x)\ \ (i=1,\dots,M)
$$

for almost every $t\in[0,T]$.

**Corollaries ($M=3$).** If $a_1$ has a unique maximizer $\bar x$, then $n_i(t,x)=\rho_i(t)\,\delta(x-\bar x)$ for $i=1,2,3$ (selection of one clone). If $\arg\max a_1=\{\bar x_1,\dots,\bar x_N\}$, each $n_i(t,\cdot)$ is a weighted sum of Dirac masses at these points (selection of several clones). If $a_1\equiv A_1$ is constant with $\tfrac12<a_2<A_1<1$, then $\operatorname{supp}n_i(t,\cdot)=[0,1]$ (no clonal selection).

## Expansion

The WKB-type variable $R_{1\varepsilon}(t,x)=\varepsilon\ln(n_{1\varepsilon}/n_1^0)$ satisfies $\partial_tR_{1\varepsilon}=P_1(\rho_{M\varepsilon},x)$, and uniform bounds on $\rho_{M\varepsilon}$ (from the feedback $1/(1+K\rho)$) make $R_{1\varepsilon}$ equi-Lipschitz. Mass bounded away from $0$ and $\infty$ forces $\max_xR_1=0$, so stem cells concentrate where $R_1$ vanishes. Since $P_1$ depends on $x$ only through $a_1(x)p_1(x)$ times a common factor $2/(1+K\rho)$ minus $p_1(x)$, and the mature mass adjusts so that the fittest stem clone has zero net growth, the selected traits are the maximizers of $a_1$. Downstream compartments are driven by upstream ones and inherit their support. The biological conclusion is that the stem-cell self-renewal fraction, not progenitor proliferation, decides which leukemic clones dominate.

## Sources

- Tommaso Lorenzi, Anna Marciniak-Czochra, Thomas Stiehl, "A structured population model of clonal selection in acute leukemias with multiple maturation stages", arXiv:1907.02842: Section 2 (model and assumptions), Section 3: Theorem 1 (general asymptotic result) and Corollaries 2–4. <https://doi.org/10.48550/arXiv.1907.02842>
