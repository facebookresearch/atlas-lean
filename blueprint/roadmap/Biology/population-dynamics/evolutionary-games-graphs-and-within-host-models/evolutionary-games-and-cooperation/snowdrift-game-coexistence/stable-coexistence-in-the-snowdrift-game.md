# Stable coexistence of cooperators and defectors in the snowdrift game

**Game.** Two strategies, cooperate ($C$) and defect ($D$), with benefit $b$ and cost $c$, $b > c > 0$. A cooperator pays the cost of producing a benefit that both players receive; two cooperators share the cost. Payoffs to the row player are

$$\begin{array}{c|cc} & C & D \\ \hline C & b - c/2 & b - c \\ D & b & 0 \end{array}$$

**Replicator dynamics.** In a large well-mixed population with cooperator frequency $x \in [0,1]$, the fitnesses are $f_C(x) = x(b - c/2) + (1-x)(b - c)$ and $f_D(x) = xb$, and the replicator equation reduces to

$$\dot x = x(1-x)\bigl(f_C(x) - f_D(x)\bigr) = x(1-x)\Bigl[(b-c) - x\bigl(b - \tfrac{c}{2}\bigr)\Bigr].$$

**Proposition.** The rest points are $0$, $1$ and

$$x^* = \frac{b-c}{b - c/2} = \frac{2(b-c)}{2b-c} \in (0,1).$$

Since $f_C - f_D > 0$ for $x < x^*$ and $< 0$ for $x > x^*$, every solution starting in $(0,1)$ converges to $x^*$: cooperators and defectors coexist stably. Both pure states are unstable, because a rare cooperator among defectors earns $b - c > 0$ and a rare defector among cooperators earns $b > b - c/2$.

**Contrast with the Prisoner's Dilemma.** If the producer keeps none of the benefit (payoffs $b-c$, $-c$, $b$, $0$), then $f_C - f_D = -c < 0$ for all $x$ and cooperation is driven to extinction. Coexistence in the snowdrift game comes from the cooperator capturing part of its own benefit, which makes cooperation advantageous when cooperators are rare.

**Biological instance.** Yeast cells that secrete invertase hydrolyse sucrose outside the cell and capture only a small fraction of the resulting glucose and fructose; mixed cultures of producers and non-producing cheaters converge to coexistence, as snowdrift-type and nonlinear public goods models predict. When population density changes on the same time scale as strain frequencies, the coupled eco-evolutionary dynamics can instead be bistable, with collapse below a threshold of cooperators.

## Depends on

- [Solution of the replicator equation](../../../replicator-dynamics/is-solution.md)
- [Rest point of the replicator equation](../../../replicator-dynamics/is-rest-point.md)

## Proof depends on

- [Rest points in the interior are equalizers](../../../replicator-dynamics/is-rest-point-iff.md)
- [Present strategies stay present](../../../replicator-dynamics/pos-of-pos.md)
- [Invariance of the simplex hyperplane](../../../replicator-dynamics/sum-eq-one.md)

## Proof sketch

For two strategies the mean fitness is $\bar f = xf_C + (1-x)f_D$, so $f_C - \bar f = (1-x)(f_C - f_D)$ and the replicator equation for $x$ is $\dot x = x(1-x)(f_C - f_D)$. The bracket is affine in $x$, positive at $x = 0$ (value $b - c$) and negative at $x = 1$ (value $-c/2$), so it has a single root $x^*$ in $(0,1)$, where the two strategies earn equal payoffs. On $(0,1)$ the factor $x(1-x)$ is positive, so $x$ increases below $x^*$ and decreases above it, and the interior rest point attracts the whole open interval.

## Sources

- B. Allen and M. A. Nowak, "Cooperation and the fate of microbial societies", PLoS Biology (2013), e1001549 (snowdrift coexistence versus extinction of cooperation in the Prisoner's Dilemma; the invertase system; eco-evolutionary feedback and bistability), <https://doi.org/10.1371/journal.pbio.1001549>, PMCID PMC3640085.
- J. Gore, H. Youk and A. van Oudenaarden, "Snowdrift game dynamics and facultative cheating in yeast", Nature 459 (2009), 253–256 (the invertase snowdrift experiment; background).
- A. Sanchez and J. Gore, "Feedback between population and evolutionary dynamics determines the fate of social microbial populations", PLoS Biology (2013), e1001547, <https://doi.org/10.1371/journal.pbio.1001547>.
- J. Hofbauer and K. Sigmund, "Evolutionary game dynamics", Bulletin of the American Mathematical Society (2003) (replicator dynamics of two-strategy games; background).
