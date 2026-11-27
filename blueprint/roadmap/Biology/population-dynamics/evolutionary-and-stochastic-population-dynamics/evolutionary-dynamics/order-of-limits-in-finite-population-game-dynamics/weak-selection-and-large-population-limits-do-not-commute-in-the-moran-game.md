# Weak-selection and large-population limits do not commute in the Moran game

**Model.** In a Moran process of size $N$ with strategies $A,B$ and payoff matrix $\begin{pmatrix}a&b\\c&d\end{pmatrix}$ (row player's payoff against $A$, $B$), the fitnesses with $i$ $A$-players are $f_A(i)=\frac{a(i-1)+b(N-i)}{N-1}$ and $f_B(i)=\frac{ci+d(N-i-1)}{N-1}$, and the fixation probability of a single $A$ is

$$\rho_A=\Big(1+\sum_{k=1}^{N-1}\prod_{j=1}^k\frac{f_B(j)}{f_A(j)}\Big)^{-1}.$$

Weak selection replaces each payoff $x$ by $1+wx$ with $w\to0$. A statement $S(N,w)$ holds in the *$wN$ limit* if $\exists N^\ast\,\forall N\ge N^\ast\,\exists w^\ast\,\forall w<w^\ast$: $S(N,w)$; it holds in the *$Nw$ limit* if $\exists w^\ast\,\forall w<w^\ast\,\exists N^\ast\,\forall N\ge N^\ast$: $S(N,w)$.

**Theorem ($wN$ limit).** In the $wN$ limit,

$$\rho_A\sim\frac1N+\frac w6(a+2b-c-2d)+o(w),$$

$\rho_A>1/N$ iff $a+2b>c+2d$ (or equality and $b>c$), and $\rho_A>\rho_B$ iff $a+b>c+d$ (or equality and $b>c$).

**Theorem (large-population limit at fixed payoffs).** For positive payoffs, with $I=\int_0^1\ln\frac{d+x(c-d)}{b+x(a-b)}\,dx$,

$$\lim_{N\to\infty}\rho_A=\begin{cases}0 & b\le d,\ \text{or } b>d,\ a<c,\ I>0,\\ \dfrac{(b-d)(c-a)}{b(c-a)+c(b-d)\sqrt{ac/(bd)}} & b>d,\ a<c,\ I=0,\\ \dfrac{b-d}{b} & b>d \text{ and } (a\ge c \text{ or } I<0).\end{cases}$$

**Corollary ($Nw$ limit).** In the $Nw$ limit, $\rho_A\sim(b-d)w+o(w)$ if $b>d$ and $a+b>c+d$; $\rho_A\sim\frac{b-d}2w+o(w)$ if $b>d$ and $a+b=c+d$; and $\rho_A=o(w)$ otherwise. Hence $\rho_A>1/N$ iff $b>d$ and $a+b\ge c+d$, or $b=d$ and $a>c$, or $b=d$, $a=c$, $b>c$. The condition $\rho_A>\rho_B$ is the same as in the $wN$ limit: $a+b>c+d$, or $a+b=c+d$ and $b>c$.

So the order of limits changes the fixation asymptotics and the criterion for beating a neutral mutant (the one-third-type rule $a+2b>c+2d$ versus $b>d$ and $a+b\ge c+d$), but not the criterion for one strategy to be favored over the other.

## Expansion

In the $wN$ order, expanding $\prod_j f_B(j)/f_A(j)$ to first order in $w$ at fixed $N$ and then letting $N\to\infty$ gives a sum of linear payoff differences averaged over the frequency path, which yields the coefficient $\frac16(a+2b-c-2d)$. In the $Nw$ order, the products behave like $\exp\big(N\int_0^{k/N}\ln\tilde f(x)dx\big)$ with $\tilde f=f_B/f_A$ in the frequency limit; the sum is dominated by its first terms when $\tilde f(0)=d/b<1$ (giving the branching-process survival probability $(b-d)/b$ of a rare mutant) and by the endpoint $x=1$ when $I$ decides whether a fitness valley is crossable. Weak selection then linearizes $(b-d)/b$ to $(b-d)w$. The ratio $\rho_A/\rho_B=\prod_jf_A(j)/f_B(j)\approx e^{-NI}$ depends on the sign of $I$, which to first order in $w$ is the sign of $c+d-a-b$ in either order.

## Depends on

- [Uniqueness of the Moran fixation probability](../../../../population-genetics/moran-model/eq-moran-fixation.md)

## Sources

- Christine Sample, Benjamin Allen, "The limits of weak selection and large population size in evolutionary game theory", arXiv:1610.07081: Definitions 1–4 (orders of limits), Theorems 1–3 ($wN$ limit), Theorem 4 and Corollary 5 (large-$N$ limit and $Nw$ asymptotics), Theorem 6 and Corollary 7 ($\rho_A>1/N$), Theorem 8 and Corollary 9 ($\rho_A>\rho_B$). <https://doi.org/10.48550/arXiv.1610.07081> Published version: Journal of Mathematical Biology (2017), <https://doi.org/10.1007/s00285-017-1119-4>.
