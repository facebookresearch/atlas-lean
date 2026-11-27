# Maximum of single-locus inbreeding depression

At a biallelic locus with genotype fitnesses $1$, $1 - hs$, $1 - s$ ($0 < s \le 1$, $h < 1/2$) for $AA$, $Aa$, $aa$, allele frequency $x$ of $A$ and $y = 1 - x$, the mean fitnesses under random mating and under inbreeding coefficient $f \in (0, 1]$ are $w_o = 1 - 2shxy - sy^2$ and $w_s = w_o - fs(1-2h)xy$, and the inbreeding depression is

$$\delta(x, f, h, s) = 1 - \frac{w_s}{w_o} = \frac{fs(1-2h)\,x(1-x)}{1 - 2x(1-x)sh - (1-x)^2 s} .$$

For partial dominance or overdominance ($h < 1/2$) and $s < 1$:

1. as a function of $x \in (0, 1)$, $\delta$ vanishes at both ends and is maximized at $x^* = \dfrac{\sqrt{1-s}}{1 + \sqrt{1-s}}$, independently of $h$ and $f$;
2. $\delta$ is strictly increasing in $f$ and in $s$, decreasing in $h$, and tends to $f$ as $h \to -\infty$.

So single-locus inbreeding depression never exceeds the inbreeding coefficient, and it approaches that bound only under strong overdominance.

## Depends on

- [Mean fitness is linear in the inbreeding coefficient](../mean-fitness-under-inbreeding.md)

## Expansion

The difference $w_o - w_s = fs(1-2h)xy$ is the linearity of mean fitness in the inbreeding coefficient. With $u = xy$,

$$\frac{f}{\delta} = \frac{1 - sy^2}{s(1-2h)\,u} - \frac{2h}{1-2h},$$

so for $h < 1/2$ maximizing $\delta$ over $x$ is the same as minimizing $(1 - s(1-x)^2)/(x(1-x))$, which does not involve $h$ or $f$; setting its derivative to zero gives $2sx(1-x)^2 = \bigl(1 - s(1-x)^2\bigr)(1 - 2x)$, whose root in $(0, 1)$ is $x^* = \sqrt{1-s}/(1 + \sqrt{1-s})$ (substitute $x = r/(1+r)$ with $r^2 = 1 - s$). As $h \to -\infty$ the second term tends to $1$ and the first to $0$, so $\delta \to f$. Low observed depression in a selfing population therefore points to loci with additive or dominant–recessive fitness effects rather than overdominance.

## Sources

- S. Sun, F. Klebaner and T. Tian, "Mathematical modelling for variations of inbreeding populations fitness with single and polygenic traits", BMC Genomics 18 (Suppl. 2) (2017) 196, <https://doi.org/10.1186/s12864-017-3492-1>, PMCID PMC5374587. Equation (3), Proposition 1 and Theorem 3.
