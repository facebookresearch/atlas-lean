# Replicator dynamics with strategy-dependent time delays

Consider a symmetric two-player game with strategies $C$ and $D$ and payoff matrix $\begin{pmatrix} a & b \\ c & d \end{pmatrix}$ with positive entries ($a,b$ are the payoffs of $C$ against $C,D$; $c,d$ those of $D$). Let $p_C(t),p_D(t)\ge 0$ be the numbers of $C$- and $D$-players, $p=p_C+p_D$, and $x=p_C/p$. The average payoffs are $U_C(t)=a x(t)+b(1-x(t))$ and $U_D(t)=c x(t)+d(1-x(t))$. Individuals die at rate $1$ and offspring of a $C$- (resp. $D$-) player appear $\tau_C\ge 0$ (resp. $\tau_D\ge 0$) time units after the game that produced them, so that

$$\frac{dp_i}{dt}=-p_i(t)+p_i(t-\tau_i)\,U_i(t-\tau_i),\qquad i=C,D.$$

The frequency $x$ then satisfies the non-closed equation

$$\frac{dx}{dt}=\frac{x(t-\tau_C)p(t-\tau_C)U_C(t-\tau_C)\bigl(1-x(t)\bigr)-\bigl(1-x(t-\tau_D)\bigr)p(t-\tau_D)U_D(t-\tau_D)\,x(t)}{p(t)},$$

coupled with $\frac{dp}{dt}=-p(t)+p_C(t-\tau_C)U_C(t-\tau_C)+p_D(t-\tau_D)U_D(t-\tau_D)$, with initial data $x=\varphi_x$, $p=\varphi_p$ on $[-\tau_M,0]$, $\tau_M=\max\{\tau_C,\tau_D\}$.

**Well-posedness.** If $\varphi_x,\varphi_p$ are continuous and non-negative, the system has a unique non-negative solution defined on $[0,\infty)$.

**Stationary frequencies.** Assume $\tau_C\neq\tau_D$ and define, for $x\in[0,1]$,

$$F(x)=\frac{1}{\tau_C-\tau_D}\ln\frac{ax+b(1-x)}{cx+d(1-x)}+1-\frac{\bigl(cx+d(1-x)\bigr)^{\tau_C/(\tau_C-\tau_D)}}{\bigl(ax+b(1-x)\bigr)^{\tau_D/(\tau_C-\tau_D)}}.$$

If $F(\bar x)=0$ and $\bar\lambda=\frac{1}{\tau_C-\tau_D}\ln\frac{a\bar x+b(1-\bar x)}{c\bar x+d(1-\bar x)}$, then $x(t)\equiv\bar x$, $p(t)=p_0e^{\bar\lambda t}$ is a solution (with the matching initial history). Thus interior stationary frequencies are the zeros of $F$ in $(0,1)$; the population grows exponentially when $\bar\lambda>0$ and dies out when $\bar\lambda<0$. In contrast with the undelayed (or equal-delay) case, where the interior rest point is the mixed Nash equilibrium $x^*=(b-d)/(b-d+c-a)$, the zeros of $F$ depend on the delays and change when a constant is added to a column of the payoff matrix.

**Example (Stag hunt).** For the payoff matrix $\begin{pmatrix} a & 0 \\ \beta a & \beta a\end{pmatrix}$ with $a>0$, $\beta\in(0,1)$, the stationary equation $F(\bar x)=0$ is solved explicitly by

$$\bar x=\left(\frac{\tau_D\,a\,\beta^{\tau_C/(\tau_C-\tau_D)}}{W_p\bigl(\tau_D\beta a e^{\tau_D}\bigr)}\right)^{(\tau_C-\tau_D)/\tau_D},$$

where $W_p$ is the principal branch of the Lambert $W$ function; this is an interior state when it lies in $(0,1)$. A positive growth rate at an interior state requires $a>1$.

## Expansion

The model comes from the discrete-time update $p_i(t+\varepsilon)=(1-\varepsilon)p_i(t)+\varepsilon p_i(t-\tau_i)U_i(t-\tau_i)$; dividing the update for $p_C$ by the one for $p$ and letting $\varepsilon\to0$ gives the frequency equation. Existence follows from the method of steps: on $[0,\tau_M]$ the delayed terms are known functions, the equation for $p$ is linear, and then the equation for $x$ is linear in $x(t)$. For a stationary state $x\equiv\bar x$ the equation for $p$ is a linear delay equation whose leading (real) eigenvalue solves $\lambda+1=\bar x\bar U_Ce^{-\lambda\tau_C}+(1-\bar x)\bar U_De^{-\lambda\tau_D}$; substituting $p=p_0e^{\lambda t}$ in the frequency equation gives $\bar U_Ce^{-\lambda\tau_C}=\bar U_De^{-\lambda\tau_D}$, so $\lambda=\ln(\bar U_C/\bar U_D)/(\tau_C-\tau_D)$, and inserting this back into the eigenvalue equation yields $F(\bar x)=0$.

## Depends on

- [Replicator dynamics](../../../replicator-dynamics/README.md)

## Proof depends on

- [Principal-branch preimages of the Lambert map](../../../../../Analysis/special-functions/elementary-transcendental-functions/lambert-w-function/exists-unique-lambert-map-preimage.md)

## Sources

- J. Miękisz and M. Bodnar, *Evolution of populations with strategy-dependent time delays*, arXiv:2102.03823 (2021), Section 2 (Propositions 1 and 2) and Section 3.1 (Stag-hunt formula). <https://doi.org/10.48550/arXiv.2102.03823>
