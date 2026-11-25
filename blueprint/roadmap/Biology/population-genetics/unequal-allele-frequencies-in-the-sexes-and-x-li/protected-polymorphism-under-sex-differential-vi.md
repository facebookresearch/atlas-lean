# Boundary invasion under sex-differential and parent-of-origin viability

Consider deterministic discrete-generation dynamics at an autosomal biallelic
locus. Eggs and sperm have $A$ frequencies $x,y\in[0,1]$, and unite
independently, giving ordered zygote probabilities $xy,x(1-y),(1-x)y,(1-x)(1-y)$.
After viability selection, each sex contributes Mendelian gametes equally
per surviving individual; there is no mutation, drift, fertility difference
among survivors or transmission distortion.
In sex $s\in\{f,m\}$ give $AA,Aa,aA,aa$ positive fixed viabilities
$w_{s,1},w_{s,2}^{\rm mat},w_{s,2}^{\rm pat},w_{s,3}$, where the first
allele is maternal. With $z_s$ the next gamete frequency in that sex,

$$z_s=\frac{w_{s,1}xy+\tfrac12w_{s,2}^{\rm mat}x(1-y)
 +\tfrac12w_{s,2}^{\rm pat}(1-x)y}
 {w_{s,1}xy+w_{s,2}^{\rm mat}x(1-y)+w_{s,2}^{\rm pat}(1-x)y
 +w_{s,3}(1-x)(1-y)},\qquad (x',y')=(z_f,z_m).$$

This map preserves the unit square. Its boundary invasion matrices are

$$A_0=\tfrac12\begin{pmatrix}
 w_{f,2}^{\rm mat}/w_{f,3}&w_{f,2}^{\rm pat}/w_{f,3}\\
 w_{m,2}^{\rm mat}/w_{m,3}&w_{m,2}^{\rm pat}/w_{m,3}
 \end{pmatrix},\qquad
 A_1=\tfrac12\begin{pmatrix}
 w_{f,2}^{\rm pat}/w_{f,1}&w_{f,2}^{\rm mat}/w_{f,1}\\
 w_{m,2}^{\rm pat}/w_{m,1}&w_{m,2}^{\rm mat}/w_{m,1}
 \end{pmatrix}.$$

$A_0$ acts on rare-$A$ frequencies near $(0,0)$; $A_1$ acts on rare-$a$
frequencies near $(1,1)$. Each boundary is locally asymptotically stable
when its matrix has spectral radius less than one and is unstable to a
positive rare-allele perturbation when that radius exceeds one. Equality
is undecided by this test. Here **protected polymorphism** means strict
mutual boundary invadability, $\rho(A_0)>1$ and $\rho(A_1)>1$, not a
claim of a unique or globally attracting interior equilibrium.

Without parent-of-origin effects, write the three viabilities as
$f_1,f_2,f_3$ and $m_1,m_2,m_3$. The spectral radii reduce to
$\tfrac12(f_2/f_3+m_2/m_3)$ and $\tfrac12(f_2/f_1+m_2/m_1)$.
They are unchanged by any positive rescaling within either sex.
For $f=(1+s,1+s/2,1)$, $m=(1,1+t/2,1+t)$ with $0<s,t<1$,
strict mutual invadability is exactly

$$s/(1+s)<t<s/(1-s).$$

In particular its small-$s$ window has $t=s+O(s^2)$.

## Depends on

- [Random union of maternal and paternal gametes](bind-map-prod-mk-apply.md)

## Expansion

The numerator lies between zero and its positive denominator, giving
closure. Differentiate at the boundaries to obtain the two matrices;
near fixation of $A$, a rare maternal $a$ corresponds to the paternal-$A$
heterozygote, explaining the reversed columns in $A_1$.
For a positive matrix $\begin{psmallmatrix}a&b\\c&d\end{psmallmatrix}$,
its larger eigenvalue is
$(a+d+\sqrt{(a-d)^2+4bc})/2>0$, exceeds the modulus of the other eigenvalue,
and has positive left and right eigenvectors. A weighted norm from the
positive left eigenvector contracts near the boundary when this value is
below one. Above one, the corresponding positive weighted rare-allele
frequency grows by a factor greater than one in a sufficiently small
neighborhood, proving instability. This is a local growth statement, not
a guarantee that each sex's frequency increases in the first generation
from every initial sex ratio. For equal heterozygote viabilities the
matrix has rank one, giving the displayed averages. Substituting the
additive fitnesses and clearing positive denominators gives the region.

## Sources

- J. F. Kidwell, M. T. Clegg, F. M. Stewart and T. Prout, "Regions of stable equilibria for models of differential selection in the two sexes under random mating", Genetics 85 (1977), 171--183, <https://doi.org/10.1093/genetics/85.1.171>, abstract. Its restricted opposing-additive-selection region motivates the example. The precise recursion, boundary tests and parent-of-origin extension above are derived here; no unnormalized average-fitness threshold or global-equilibrium theorem is attributed to the abstract.
