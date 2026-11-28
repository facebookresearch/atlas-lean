# Interior critical points of memory-one adaptive dynamics are equalizers

**Setting.** In the repeated donation game with benefit $b$ and cost $c$, $b>c>0$ (payoffs $R=b-c$, $S=-c$, $T=b$, $P=0$, so $R+P=S+T$: equal gains from switching), a memory-one strategy is $p=(p_{CC},p_{CD},p_{DC},p_{DD})\in[0,1]^4$, the probability of cooperating after each outcome of the previous round (own move first). For $p,p'\in(0,1)^4$ the pair of strategies induces an ergodic Markov chain on $\{CC,CD,DC,DD\}$ with stationary law $v$, and the repeated-game payoff is $A(p,p')=Rv_{CC}+Sv_{CD}+Tv_{DC}+Pv_{DD}$. *Adaptive dynamics* moves a homogeneous population up the selection gradient,

$$\dot p_{ij}=\frac{\partial A(p,p')}{\partial p_{ij}}\Big|_{p'=p},\qquad i,j\in\{C,D\}.$$

A strategy $p$ is an *equalizer* if $A(p',p)$ does not depend on $p'$: it fixes the co-player's payoff.

**Theorem.**

(1) An interior strategy $p\in(0,1)^4$ is a critical point of the adaptive dynamics if and only if

$$b\,(p_{CC}-p_{CD})-c\,(1-p_{CC}+p_{DC})=0\qquad\text{and}\qquad p_{CC}+p_{DD}=p_{CD}+p_{DC}.$$

The interior critical set is therefore a two-dimensional plane section of the cube, on which $p_{CC}>c/b$ and $p_{DD}<1-c/b$.

(2) Every interior critical point is an equalizer, and every equalizer is a critical point. Since equalizers are exactly the Nash equilibria among stochastic memory-one strategies of the donation game, an interior point is critical for adaptive dynamics if and only if it is a Nash equilibrium.

(3) *Counting strategies.* For the adaptive dynamics on the cube of counting strategies $q=(q_2,q_1,q_0)$ (cooperation probability after $2,1,0$ cooperators), the interior critical points are exactly

$$\Big(t+\frac{c}{b+c},\ t,\ t-\frac{c}{b+c}\Big),\qquad t\in\Big(\frac{c}{b+c},\frac{b}{b+c}\Big),$$

a segment on which $q_1=(q_2+q_0)/2$.

## Expansion

With the factorized form $\dot p_{ij}\propto f_{ij}(b\,g_{ij}+c\,h_{ij})$ and the $f_{ij}$ nonvanishing in the interior, critical points solve a polynomial system that reduces to the two linear equations in part 1, which coincide with the known linear characterization of equalizer strategies for donation-game payoffs. An equalizer makes $A(p',p)$ constant in $p'$, so in particular the gradient in the first argument at $p'=p$ vanishes; the content of part 2 is the converse. For counting strategies, combining the component equations gives $\dot q_1/f_1+\dot q_0/f_0=(b-c)(q_0-q_1)(q_2-2q_1+q_0)$ and $\dot q_2/f_2-\dot q_0/f_0=(b-c)(q_2-q_0)(q_2-2q_1+q_0)$, forcing $q_1=(q_2+q_0)/2$; substituting back leaves $b(q_0-q_2)+c(2+q_0-q_2)=0$, i.e. $q_2-q_0=2c/(b+c)$, and the interior constraint gives the range of $t$. Because these critical points are not attractors in general, the paper's further boundary analysis determines where cooperative strategies are locally stable, a condition weaker than being a Nash equilibrium.

## Depends on

- [Invariance of counting strategies and time-reversal duality](invariance-of-counting-strategies-and-time-reversal-duality.md)
- [Is singular](../../../classification-of-adaptive-dynamics-singular-str/is-singular.md)

## Sources

- LaPorte P, Hilbe C, Nowak MA. Adaptive dynamics of memory-one strategies in the repeated donation game. *PLoS Computational Biology* 19 (2023). <https://doi.org/10.1371/journal.pcbi.1010987> (PMCID: PMC10337984). Eq. (9); Propositions 3, 4 and 5 in Methods.
