# Delay-induced shift and uniqueness of the interior stationary state

Work in the replicator model with strategy-dependent delays $\tau_C\ne\tau_D$, payoff matrix $\begin{pmatrix} a & b \\ c & d\end{pmatrix}$ with positive entries, stationary-state function $F$ and growth rate $\lambda(\bar x)=\frac{1}{\tau_C-\tau_D}\ln\frac{a\bar x+b(1-\bar x)}{c\bar x+d(1-\bar x)}$. Assume a Snowdrift-type game, $a<c$ and $d<b$, so that the undelayed mixed equilibrium is $x^*=(b-d)/(b-d+c-a)\in(0,1)$.

1. **Shift away from the slower strategy.** Let $\bar x\in(0,1)$ be a stationary frequency with $\lambda(\bar x)>0$. If $\tau_C>\tau_D$ then $\bar x<x^*$; if $\tau_C<\tau_D$ then $\bar x>x^*$. A strategy whose offspring arrive later is less frequent at a growing interior equilibrium than without delays.

2. **Sign of $F$ at the boundary.** Suppose $\tau_C>\tau_D$ and set $u=(a/c)^{\tau_C/(\tau_C-\tau_D)}\in(0,1)$ and $u^*=a\tau_C/W_p(a\tau_Ce^{\tau_C})$, with $W_p$ the principal Lambert $W$ branch. Then $F(1)>0$ if and only if $a<1$ and $u>u^*$; in particular $F(1)<0$ whenever $a\ge1$. An interior zero of $F$ exists whenever $F(0)$ and $F(1)$ have opposite signs.

3. **Monotonicity and uniqueness.** If in addition $a<d<c$ or $d<a<b$, then $F$ is strictly monotone on $[0,1]$: decreasing if $\tau_C>\tau_D$ and increasing if $\tau_C<\tau_D$. Hence there is at most one interior stationary frequency, and exactly one if $F(0)F(1)<0$. The same holds if $a=b$ or $c=d$.

## Expansion

(1) For $\tau_C>\tau_D$ the sign of $\lambda$ is that of $\phi(x)=\ln\frac{ax+b(1-x)}{cx+d(1-x)}$, which vanishes at $x^*$ and has $\phi'(x)=\frac{ad-bc}{(ax+b(1-x))(cx+d(1-x))}<0$ because $ad<bc$; so $\lambda>0$ forces $\bar x<x^*$. The case $\tau_C<\tau_D$ flips the sign. (2) Writing $a=zc$ with $z\in(0,1)$ turns $F(1)$ into $f_a(u)=\tau_C^{-1}\ln u+1-a/u$, strictly increasing from $-\infty$ with $f_a(1)=1-a$; its root solves $(a\tau_C/u)e^{a\tau_C/u}=a\tau_Ce^{\tau_C}$, i.e. $u=u^*$. (3) Differentiating,

$$F'(x)=\frac{1}{\tau_C-\tau_D}\left(\frac{ad-bc}{U_C U_D}+\Bigl(\tau_C(d-c)+\tau_D(a-b)\tfrac{U_D}{U_C}\Bigr)\Bigl(\tfrac{U_D}{U_C}\Bigr)^{\tau_D/(\tau_C-\tau_D)}\right),$$

with $U_C=ax+b(1-x)$, $U_D=cx+d(1-x)$; under the stated orderings every bracketed term is negative, so the sign of $F'$ is the sign of $-(\tau_C-\tau_D)$.

## Depends on

- [Replicator dynamics with strategy-dependent time delays](replicator-dynamics-with-strategy-dependent-time-delays.md)

## Proof depends on

- [Principal-branch preimages of the Lambert map](../../../../../Analysis/special-functions/elementary-transcendental-functions/lambert-w-function/exists-unique-lambert-map-preimage.md)

## Sources

- J. Miękisz and M. Bodnar, *Evolution of populations with strategy-dependent time delays*, arXiv:2102.03823 (2021), Appendix A.1: Proposition A.2, Theorem A.3 (part A), Theorem A.6 and Corollary A.7. <https://doi.org/10.48550/arXiv.2102.03823>
