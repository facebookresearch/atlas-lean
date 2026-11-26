# Rejuvenation interval and replicative lifespan of asymmetrically dividing cells

**Model.** The biological age of a mother cell (for example a budding yeast cell) is the number $\xi_t\in\{0,\dots,n\}$ of harmful proteins it carries, with $n$ the senescence state, which is absorbing. In each time step a cell of age $i<n$ receives $\tau$ new harmful proteins ($\tau\ge0$ integer-valued), then divides with probability $b_{i+\tau}$. Without division its age becomes $(i+\tau)\wedge n$. At division each of the $i+\tau$ proteins is retained by the mother with probability $p$ and passed to the daughter otherwise, so the mother's age becomes $B\wedge n$ with $B\sim\mathrm{Bin}(i+\tau,p)$ and the daughter is born with age $(i+\tau-B)\wedge n$. A state $i$ is a *rejuvenation state* if the expected jump $d_i=\mathbb E[\xi_{t+1}-\xi_t\mid\xi_t=i]$ is negative.

**General criterion.** If $b_i=0$ for $i\ge n$, then $\mathbb E[\xi_{t+1}\mid\xi_t=i]=\mathbb E\bigl[(i+\tau)\wedge n-(1-p)(i+\tau)b_{i+\tau}\bigr]$, so $i\in\{1,\dots,n-1\}$ is a rejuvenation state if and only if
$$\mathbb E[\tau\wedge(n-i)]<(1-p)\,\mathbb E\bigl[(i+\tau)\,b_{i+\tau}\bigr].$$

**The $(m,\alpha)$-case.** Take a constant inflow $\tau\equiv m\in\{1,\dots,n-1\}$ and division probabilities $b_i=1-(i/n)^\alpha$ for $0\le i\le n$, $\alpha\ge1$. Then $d_i=n-i$ for $n-m\le i\le n$ and
$$d_i=m-(1-p)(i+m)\Bigl(1-\bigl(\tfrac{i+m}n\bigr)^\alpha\Bigr),\qquad0\le i<n-m.$$
The set of rejuvenation states is either empty or an interval $i_1\le i\le i_2$ with $0<i_1\le i_2<n-m$, where
$$i_1=\lceil ny_1\rceil-m,\qquad i_2=\lfloor ny_2\rfloor-m,$$
and $y_1<y_2$ are the two roots in $(0,1)$ of $y-y^{1+\alpha}=\dfrac{m}{(1-p)n}$. The interval shrinks when the retention $p$ or the inflow $m$ increases and widens when the division rate $\alpha$ increases. For $n=100$, $m=15$, $p=0.5$, $\alpha=2$ the equation is $y-y^3=0.3$ and the rejuvenation states are $19\le i\le63$.

**Replicative lifespan.** Let $L$ be the number of divisions before senescence and $\lambda_i=\mathbb E[L\mid\xi_0=i]$. With $P_0=(p_{ij})_{0\le i,j<n}$ the transition matrix restricted to non-senescent states and $\beta_i=\mathbb E[b_{i+\tau}]$, first-step analysis gives
$$\lambda=(I-P_0)^{-1}\beta .$$
In the $(m,\alpha)$-case $\lambda_i$ decreases in the current age $i$, in $p$ and in $m$, and increases in $\alpha$.

## Expansion

The expected-jump formula follows from $\mathbb E[B]=p(i+\tau)$: division removes on average $(1-p)(i+\tau)$ proteins with probability $b_{i+\tau}$, while the inflow adds $\tau$ up to the cap $n$. In the $(m,\alpha)$-case, with $y=(i+m)/n$ the condition $d_i<0$ reads $y-y^{1+\alpha}>m/((1-p)n)$; the left side is concave on $(0,1)$ and vanishes at both ends, so the solution set is an interval between its two roots, empty when the maximum $\alpha(1+\alpha)^{-1-1/\alpha}$ does not exceed $m/((1-p)n)$. The same Markov chain, together with the daughter's age at birth, defines a multitype Galton–Watson process indexed by biological age, from which the source derives the stable age distribution and the average biological age of a growing population.

## Sources

- S. Sagitov, L. Eriksson and M. Cvijovic, *A multitype Galton-Watson model for rejuvenating cells*, arXiv:2402.07111 (2024): Section 2 (transition probabilities and the rejuvenation criterion), Section 3 (the $(m,\alpha)$-case: expected jump sizes, the rejuvenation interval and its monotonicity), Section 4 (expected replicative lifespan and its monotonicity), Section 5 (the multitype Galton–Watson process). <https://doi.org/10.48550/arXiv.2402.07111>
