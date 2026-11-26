# Switching probability thresholds for replicator phase portraits and Moran fixation

A population of two types lives in environment $E_1$ (game matrix $A_1$) with probability $p$ and in $E_2$ (game matrix $A_2$) with probability $1-p$. Its mean dynamics are the replicator equation $\dot x_i=x_i\big((Ax)_i-x\cdot Ax\big)$ for the averaged matrix

$$
A(p)=pA_1+(1-p)A_2 .
$$

For $A=\begin{pmatrix}a&b\\c&d\end{pmatrix}$, the non-degenerate phase portraits are P1 ($a\le c$, $d\ge b$), P2 ($a\ge c$, $d\le b$), Hawk–Dove HD ($a<c$, $d<b$; stable interior rest point $\hat x=(d-b)/(d-b+a-c)$), and Coordination Co ($a>c$, $d>b$; unstable interior rest point).

**Theorem (portrait switching).** Let $E_1,E_2\in\{\mathrm{P1},\mathrm{P2},\mathrm{HD},\mathrm{Co}\}$ and $p^*\in(0,1)$. For every game matrix $A_1$ with portrait $E_1$ there are infinitely many matrices $A_2$ with portrait $E_2$ such that $A(p)$ has portrait $E_2$ for $0<p<p^*$ and portrait $E_1$ for $p^*<p<1$. (The source states the two intervals the other way round; since $A(0)=A_2$ and $A(1)=A_1$, its construction yields the orientation given here.)

**Constant relative fitness.** If type 1 has relative fitness $s$ in $E_1$ and $t$ in $E_2$ (matrix rows $(r,r)$ and $(1,1)$), the averaged fitness is $r=ps+(1-p)t$, and the replicator dynamic fixes type 1 if and only if

$$
p\,(s-t)>1-t .
$$

In the Moran process of size $N$ driven by the averaged landscape, a single type-1 mutant fixes with probability

$$
\phi=\frac{1-r^{-1}}{1-r^{-N}},\qquad r=p(s-t)+t,
$$

so for large $N$ and $r>1$, $\phi\approx1-1/r$, and fixation becomes more likely than not only when $r>2$, i.e. $p>(2-t)/(s-t)$ for $s>t$. The stochastic threshold exceeds the deterministic one by $1/(s-t)$: with $s=3$, $t=1/2$, the replicator dynamic fixes the mutant for $p>2/5$, but likely fixation in the Moran process needs $p>3/5$.

## Depends on

- [Lyapunov characterization of evolutionarily stable states for the replicator equation](../../population-dynamics/replicator-dynamics/ess-lyapunov-function-for-the-replicator-equation.md)

## Expansion

The portrait of a $2\times2$ replicator dynamic depends only on the signs of $a-c$ and $d-b$, which can be chosen independently, and adding a constant to a column leaves it unchanged. To move the sign of $a-c$ at $p^*$, keep $b_2=b_1$, $d_2=d_1$, choose $a_2$ freely and set $c_2=a_2-\frac{p^*}{1-p^*}(c_1-a_1)$, so that $a(p)-c(p)$ vanishes exactly at $p=p^*$; the column freedom gives infinitely many choices. The constant-fitness statements follow from $r=ps+(1-p)t$ and the classical Moran fixation probability $(1-r^{-i})/(1-r^{-N})$ from $i$ copies. Here the mean dynamics average over environment sequences; they do not model whole generations spent in one environment, which can select the locally adapted type much more strongly.

## Sources

- Marc Harper, Dashiell Fryer and Andrew Vlasic, *Mean evolutionary dynamics for stochastically switching environments*, arXiv:1306.2373 (2013), Theorem 1 and Section 2 (inequality (1)), Section 4 (Moran fixation probability). <https://doi.org/10.48550/arXiv.1306.2373>
