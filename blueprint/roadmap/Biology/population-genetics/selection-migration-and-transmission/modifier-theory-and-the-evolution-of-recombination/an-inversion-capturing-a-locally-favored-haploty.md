# Local invasion of a recombination-suppressing inversion at an island equilibrium

Use deterministic two-locus haplotype frequencies
$x=(x_1,x_2,x_3,x_4)$ on the simplex for $AB,Ab,aB,ab$.
In each generation replace fraction $m\in[0,1)$ by $ab$ migrants, giving
$z=(1-m)x+m(0,0,0,1)$. Apply fixed positive haplotype viabilities $w_i$,
with $\bar w=\sum_iw_iz_i$ and $y_i=w_iz_i/\bar w$.
Finally use random union and recombination fraction $0\le r\le1/2$:

$$x'=(y_1-rD,y_2+rD,y_3+rD,y_4-rD),\qquad
 D=y_1y_4-y_2y_3.$$

Let $x^*$ be any resident equilibrium with $x_1^*>0$.
A rare inversion carries $AB$, has the same viability $w_1$, is absent
from migrants, and suppresses recombination with standard chromosomes.
Assume no segregation disadvantage or other direct cost. Its linearized
rare frequency multiplier is

$$\lambda=(1-m)w_1/\bar w^*=1+rD^*/x_1^*.$$

Thus it invades ($\lambda>1$) exactly when $rD^*>0$, declines
($\lambda<1$) exactly when $rD^*<0$, and is neutral to first order when
$rD^*=0$. For $r>0$ these signs are precisely the signs of post-selection
linkage disequilibrium $D^*$. At $r=0$ even negative $D^*$ gives neutrality,
not decline. The test assumes an equilibrium; it does not prove that one
with $D^*>0$ exists or that the inversion fixes after invasion.

## Expansion

Migration and selection preserve the simplex. For recombination,
$y_1-rD=y_1(1-r y_4)+r y_2y_3\ge0$, and the other coordinates have
analogous expressions; total mass remains one.
Under the specified inversion inheritance rule, its frequency after
migration and selection is multiplied by $(1-m)w_1/\bar w$ and is unchanged
by recombination. Differentiating at zero inversion frequency gives the
first expression for $\lambda$. The resident equation
$x_1^*=y_1^*-rD^*$ with
$y_1^*=(1-m)w_1x_1^*/\bar w^*$ gives the second.
With $m=0$, $r=0$ and all $w_i=1$, every resident vector is an equilibrium;
$x=(1/10,2/5,2/5,1/10)$ has $D<0$ but $\lambda=1$.
Zero recombination preserves linkage disequilibrium only in the
recombination step; preceding migration and selection can change it.

## Sources

- M. Kirkpatrick and N. Barton, "Chromosome inversions, local adaptation and speciation", Genetics 173 (2006), 419--434, <https://doi.org/10.1534/genetics.105.047985>, abstract. The explicit haploid island model and its local identity are derived here; diploid heterokaryotype costs and later fixation require different results.
