# Descriptor-divergence aggregation of the GuacaMol suite

A generator should reproduce the spread of a library. The distribution-learning suite compares generated and reference distributions of several physicochemical descriptors and averages the exponentials of their divergences; this page states that aggregation.

Let $k \ge 1$ and let $D_1, \dots, D_k \in [0, \infty]$ be supplied divergence values, $D_i$ comparing the generated and the reference distribution of descriptor $i$. With the convention $\exp(-\infty) = 0$, the score is

$$
S = \frac{1}{k} \sum_{i=1}^{k} \exp(-D_i) .
$$

Then $0 \le S \le 1$; $S = 1$ exactly when every $D_i = 0$ and $S = 0$ exactly when every $D_i = \infty$. As one value $D_j \to \infty$ with the others fixed,

$$
S \longrightarrow \frac{1}{k} \sum_{i \neq j} \exp(-D_i) ,
$$

which is positive exactly when some other component is finite: for $k = 1$, and for $k > 1$ with every other value already infinite, the limit is zero, while for $k = 2$ with the other value zero it is $1/2$.

This page states the aggregation on supplied values as the corresponding component of the chemical evaluation protocol; it defines neither the divergences nor the benchmark as a whole. Three things an implementation must pin. The divergences are Kullback–Leibler divergences in the extended sense, which a measure-theoretic definition supplies; for two distributions on a common finite set of histogram bins the divergence is infinite exactly when the numerator distribution puts positive mass on a bin where the denominator puts none, so unequal supports alone do not make it infinite, as $P = (1,0)$ against $Q = (1/2,1/2)$ shows with value $\log 2$, while in general finiteness also needs the log-likelihood ratio to be integrable, and the two directions are not interchangeable. The distributions are estimates, by kernel density for a continuous descriptor and by a histogram for a discrete one, so bandwidth, binning and smoothing belong to the benchmark. And the components are ambiguous in the source, which prints $k = 9$ while listing nine toolkit descriptors (molecular complexity, the logarithm of the octanol–water partition coefficient, molecular weight, topological polar surface area, counts of hydrogen-bond acceptors and donors, rotatable bonds, aliphatic rings and aromatic rings) together with a tenth distribution, of maximum nearest-neighbour fingerprint similarities; the direction of each divergence is likewise not labelled there.

## Depends on

None.

## Proof depends on

None.

## Expansion

A formal development takes $k \ge 1$ values in $[0, \infty]$ and defines $S$ by the display with $\exp(-\infty) = 0$. The bounds and both equality cases follow from $0 \le \exp(-x) \le 1$ on $[0,\infty]$ with equality at the endpoints, and the saturation limit from continuity of the finite sum, with positivity of the limit exactly when some other component is finite. A page that also defines the divergences would take the measure-theoretic Kullback–Leibler divergence, with its absolute-continuity and integrability conventions, as a statement prerequisite.

## Context

Undergraduate to graduate; the aggregation step of a benchmark. Introduced with the distribution-learning suite of Brown, Fiscato, Segler and Vaucher as the component that penalizes a generator for collapsing onto a narrow region of chemical space.

## Sources

- Nathan Brown, Marco Fiscato, Marwin H. S. Segler and Alain C. Vaucher, *GuacaMol: Benchmarking Models for de Novo Molecular Design*, Journal of Chemical Information and Modeling 59 (2019) 1096–1108, Section 3.1.5 and the appendix implementation details, which print the aggregation, the descriptor list and $k = 9$ alongside the extra nearest-neighbour-similarity distribution. DOI [10.1021/acs.jcim.8b00839](https://doi.org/10.1021/acs.jcim.8b00839), arXiv:[1811.09621v2](https://arxiv.org/abs/1811.09621v2).
