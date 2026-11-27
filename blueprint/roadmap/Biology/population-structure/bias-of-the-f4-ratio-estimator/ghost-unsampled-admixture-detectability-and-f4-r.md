# Ghost admixture: a nonzero f4, a positive f3 and a biased f4 ratio

There is an explicit [drift model](../patterson-s-f-statistics/drift-model.md) with an unsampled donor in which the sampled populations violate a specified quartet null, have a positive target f3, and give an f4 ratio different from the donor proportion. These are population-statistic identities, not a finite-sample significance test or unique identification of the donor.

## Construction

Take a root with three outgoing branches: an outgroup leaf edge $e_O$ to $O$, an edge $a$ to $u$, and an edge $g$ to $h$. From $u$ come $Z$ along $e_Z$ and $v$ along $b$; from $v$ come $Y$ along $e_Y$ and an unsampled $X'$ along $e_X$. From $h$ come sampled $B$ along $e_B$ and $k$ along $g_2$; from $k$ come sampled $A$ along $e_A$ and the unsampled donor $G$ along $g_3$. Thus $G$ branches outside the $X',Y,Z$ subtree. Let every edge have length $1$ except $\ell_{e_O}=2$. The sampled $X$ is the mixture of $G$ and $X'$ with donor proportion $\alpha=3/10$, without subsequent drift.

Writing a sum of edge names for its path-indicator vector, the weights are

$$w_Y=a+b+e_Y,\quad w_Z=a+e_Z,\quad w_{X'}=a+b+e_X,\quad w_B=g+e_B,$$

$$w_A=g+g_2+e_A,\quad w_G=g+g_2+g_3,\quad w_O=e_O,\quad w_X=\alpha w_G+(1-\alpha)w_{X'}.$$

This is an actual square-integrable model: on the uniform space of twelve independent signs, use ten signs as the unit-length increments and the sum of the remaining two signs as the increment on $e_O$. Distinct edge increments are orthogonal, and their second moments are exactly the assigned lengths. Add any constant common root frequency. The raw model is real-valued; a bounded-frequency version uses root $1/2$ and divides every increment by $8$. Every ancestral and sampled frequency then lies in $[1/8,7/8]$, all drift lengths and f-statistics are divided by $64$, and the ratio is unchanged.

## Exact statistics and interpretation

The [f3](../patterson-s-f-statistics/f3-freq.md) and [f4](../patterson-s-f-statistics/f4-freq.md) drift formulas give, for the unscaled lengths,

$$f_4(X,Y;Z,O)=-\alpha=-\frac{3}{10},\qquad f_3(X;Y,Z)=6\alpha^2-3\alpha+1=\frac{16}{25}.$$

At $\alpha=0$, $X=X'$ and the $XY\mid ZO$ quartet has f4 equal to zero. The displayed nonzero value is a signal against that specified null without sampling $G$. It does not identify the donor, the direction of gene flow, or admixture uniquely among all demographic models. The positive f3 supplies no negative-f3 certificate with these references; it does not assert that every three-population analysis must fail.

For the proxy ratio, direct calculation gives

$$f_4(A,O;G,Y)=2,\quad f_4(A,O;B,Y)=1,\quad f_4(A,O;X',Y)=0.$$

The last cancellation is essential: the mixture baseline is $X'$, not $Y$. Bilinearity yields

$$f_4(A,O;X,Y)=\alpha f_4(A,O;G,Y)+(1-\alpha)f_4(A,O;X',Y)=2\alpha,$$

so $f_4(A,O;X,Y)/f_4(A,O;B,Y)=3/5=2\alpha$. To use the existing [bias-factor identity](f4-ratio-eq-mul-div.md), first take its mixture baseline to be $X'$; the zero contrast then allows replacement of $X'$ by $Y$ in these f4 expressions. It would be incorrect to assume $w_X=\alpha w_G+(1-\alpha)w_Y$. The factor is $2$ because $A$ shares both $g$ and $g_2$ with $G$, but only $g$ with $B$. The proxy equality required for [ratio identification](../patterson-s-f-statistics/f4-ratio.md) fails even though the denominator is nonzero.

## Depends on

- [Admixture-graph drift model](../patterson-s-f-statistics/drift-model.md)
- [f4 statistic](../patterson-s-f-statistics/f4.md)

## Proof depends on

- [f3 in the drift model](../patterson-s-f-statistics/f3-freq.md)
- [f4 in the drift model](../patterson-s-f-statistics/f4-freq.md)
- [Bias factor of the f4 ratio in the drift model](f4-ratio-eq-mul-div.md)

## Related

- [f4-ratio estimation of the admixture proportion](../patterson-s-f-statistics/f4-ratio.md)

## Sources

- N. Patterson et al., *Ancient admixture in human history*, Genetics 192 (2012), 1065–1093, <https://pmc.ncbi.nlm.nih.gov/articles/PMC3522152/>, sections on the three-population test, D-statistics and f4-ratio estimation, especially equations (4)–(5). These provide the definitions and interpretation; the explicit graph, arithmetic and bounded realization above are derived here.
