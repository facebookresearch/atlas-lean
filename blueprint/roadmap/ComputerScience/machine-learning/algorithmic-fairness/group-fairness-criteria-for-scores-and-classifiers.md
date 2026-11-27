# Group fairness criteria for scores and classifiers

Let $(X,A,Y)$ be jointly distributed, with $Y\in\{0,1\}$ and a group attribute $A$ in a finite nonempty set
$G$. Use the support of $A$ as $G$, so $\Pr[A=a]>0$ for each $a\in G$. Let $S\in[0,1]$ be a possibly randomized
score computed from the observed data. Common criteria are:

- Calibration within groups: $\mathbb{E}[Y\mid S,A]=S$ almost surely. For discrete scores this is equivalent to
    $\Pr[Y=1\mid S=s,A=a]=s$ at every pair $(s,a)$ of positive probability; no condition is imposed through a
    zero-probability conditioning event.
- Balance for the positive class: assuming $\Pr[A=a,Y=1]>0$ for every $a\in G$, the means
    $\mathbb{E}[S\mid Y=1,A=a]$ are equal across groups. Balance for the negative class is defined analogously,
    with $Y=0$ and the corresponding strictly positive joint class masses.
- Equalized odds: $S$ and $A$ are conditionally independent given $Y$.
- Statistical parity: $S$ and $A$ are independent.

Each balance criterion above is stated on its positive-mass domain; it assigns no conditional mean to an empty
group/class cell. The almost-sure calibration formulation also applies to continuous scores.

## Sources

- J. Kleinberg, S. Mullainathan and M. Raghavan, *Inherent trade-offs in the fair determination of risk scores*, ITCS 2017; arXiv:1609.05807, conditions (A), (B) and (C). <https://arxiv.org/pdf/1609.05807>
- M. Hardt, E. Price and N. Srebro, *Equality of opportunity in supervised learning*, NeurIPS 2016, Definition 2.1. <https://home.ttic.edu/~nati/Publications/HardtPriceSrebro2016.pdf>
