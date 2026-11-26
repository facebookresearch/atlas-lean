# Minimum description length bound with description length in nats

Let $X$, $Y$ be measurable spaces, $C$ a class of hypotheses $X \to Y$ with measurable misclassification sets, and $d : C \to \{0,1\}^*$ a prefix-free description (for distinct $h \ne h'$, $d(h)$ is not a prefix of $d(h')$; in particular $d$ is injective); write $|d(h)|$ for its length in bits. For every distribution $D$ on $X \times Y$, $m > 0$ and $\delta > 0$, with probability at least $1 - \delta$ over $S \sim D^m$, every $h \in C$ satisfies

$$
|L_S(h) - L_D(h)| \le \sqrt{\frac{|d(h)| \ln 2 + \ln(2/\delta)}{2m}},
$$

where $L$ denotes the 0-1 error. In particular $L_D(h) \le L_S(h) + \sqrt{(|d(h)|\ln 2 + \ln(2/\delta))/(2m)}$, which sharpens the bound with $|d(h)| + \ln(2/\delta)$ since $\ln 2 < 1$.

## Proof sketch

By Kraft's inequality the weights $w(h) = 2^{-|d(h)|}$ sum to at most $1$. Hoeffding's inequality gives each singleton $\{h\}$ the uniform convergence rate $\sqrt{\ln(2/\delta)/(2m)}$, and the weighted union bound of structural risk minimization at confidence $w(h)\delta$ for $h$ yields the claim, since $\ln(1/w(h)) = |d(h)|\ln 2$.

## Depends on

- [Minimum description length bound](../../pac-learning/minimum-description-length-bound.md)
- [Kraft's inequality for prefix codes](../../../../InformationTheory/source-coding/kraft-mcmillan-lengths.md)

## Proof depends on

- [Kraft's inequality for prefix codes](../../../../InformationTheory/source-coding/kraft-mcmillan-lengths.md)
- [Two-sided Hoeffding inequality for averages of bounded variables](../../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-abs-avg-sub-ge-le.md)
- [Nonuniform learnability and structural risk minimization](../../pac-learning/nonuniform-learnability-and-structural-risk-minimization.md)

## Sources

- S. Shalev-Shwartz and S. Ben-David, "Understanding Machine Learning: From Theory to Algorithms", Cambridge University Press, 2014.
- L. G. Kraft, "A Device for Quantizing, Grouping, and Coding Amplitude-Modulated Pulses", Master's thesis, Massachusetts Institute of Technology, 1949.
