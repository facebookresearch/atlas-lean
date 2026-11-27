# Steady-state lead of the fitness distribution under beneficial mutation-selection balance

In the concurrent-mutations regime of an asexual population of size $N$ with beneficial mutation rate
$U_b$ and common mutation effect $s$, the lead $qs$ of the fitness distribution settles at the value that
balances mutation, which pushes the nose forward, against selection, which moves the mean forward.
Requiring that the subpopulation sizes, which decrease geometrically from the class nearest the mean out
to the nose, sum to $N$, and taking every establishment interval to equal its mean $\langle \tau_q\rangle$,
gives the transcendental equation

$$q \approx \frac{2\ln[Nqs]}{\ln\bigl[(s/U_b)\bigl((q-1)\sin(\pi/q)/(\pi e^{\pi/q})\bigr)\bigr]} .$$

Because $q$ appears only inside logarithms on the right, iteration converges quickly, and the zeroth
iterate

$$q \approx \frac{2\ln[Ns]}{\ln[s/U_b]}$$

is accurate enough for most purposes. The lead grows with $N$, since in a larger population the less-fit
classes take longer to be eliminated and more mutations accumulate meanwhile, and grows with $U_b$, since
mutations then arrive faster at the nose. Its dependence on $s$ is not monotone in an obvious way,
because increasing $s$ shortens the fixation time while raising the establishment probability.

## Depends on

- [Establishment interval at the nose of the fitness distribution](establishment-interval-at-the-nose.md)
- [Successional and concurrent regimes of beneficial mutations in an asexual population](successional-and-concurrent-mutation-regimes.md)

## Proof depends on

- [Establishment interval at the nose of the fitness distribution](establishment-interval-at-the-nose.md)

## Expansion

Just after the class at lead $qs$ establishes, its size is $1/(qs)$, the class one step behind is larger
by a factor set by its exponential growth over the interval $\langle \tau_q\rangle$, and so on down the
distribution; the total is dominated by the largest class, the one closest to the mean fitness, so
equating that class to $N$ fixes the relation between $q$ and $N$. Substituting the mean establishment
interval produces the displayed equation. The analysis holds only for $q > 2$: at smaller leads the
feeding class saturates while the next class is establishing, and the crossover to the
successional-mutations regime begins.

## Sources

- M. M. Desai and D. S. Fisher, "Beneficial mutation-selection balance and the effect of linkage on positive selection", Genetics 176 (2007), 1759-1798, <https://doi.org/10.1534/genetics.106.067678> (PMC1931526). (Equations 39 and 40.)
