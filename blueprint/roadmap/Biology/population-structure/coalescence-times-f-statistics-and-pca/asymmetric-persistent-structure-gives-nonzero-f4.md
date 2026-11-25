# Four-deme stepping-stone times and their f4 contrast

Let four demes of equal scaled size one, $P_1,P_2,P_3,O$, occupy a line in that order.
Each lineage moves to each neighboring deme at rate $m>0$; two lineages
in the same deme coalesce at rate one. Write $T_{ij}$ for the expected
coalescence time from demes $i,j$, with $O=4$. The fourth deme is not
an isolated outgroup: it exchanges migrants with deme $3$.
The finite killed-pair model has finite means, and

$$T_{14}+T_{23}-T_{13}-T_{24}=-\frac1{m(16m+7)}.$$

For any canonical coalescent model on a **finite** site measure with
these $T_{ij}$ and mutation parameter $\theta>0$, its heterozygosity-time
relation and the canonical $f_4$ identity therefore give

$$f_4(P_1,P_2;P_3,O)=-\frac{\theta}{2m(16m+7)}<0.$$

At $m=1$ this is $-\theta/46$; for fixed $\theta$, it tends to zero as
$m\to\infty$. For $\theta=0$ it is zero, not a nonzero counterexample.
This history has ongoing migration but no pulse event. Conditional on
the stated model bridge, a nonzero contrast therefore does not by
itself identify a **pulse** of admixture. It is not evidence for an
absence of gene flow or a violation of an isolated-outgroup model's
conclusions while preserving that model's hypotheses.

## Depends on

- [General killed-pair model and first-step equations](../../coalescent-theory/structured-coalescent/strobeck-nagylaki-invariance-size-weighted-mean.md)
- [Coalescent model and its heterozygosity-time assumption](coalescent-model.md)
- [Definition of f4](../patterson-s-f-statistics/f4.md)

## Proof depends on

- [f4 in terms of mean coalescence times](f4-eq.md)

## Expansion

The migration generator is symmetric and irreducible for $m>0$, with
uniform stationary law. The general killed-pair argument supplies
finite absorption means and a unique solution of the first-step
system. Exchange of the two lineages and reflection of the line leave
six classes:

$$T=\begin{pmatrix}
a&c&d&e\\c&b&h&d\\d&h&b&c\\e&d&c&a
\end{pmatrix}.$$

Writing $q=16m+7$, their values are

$$\begin{aligned}
a&=(64m+20)/q,& b&=(64m+36)/q,\\
c&=(128m^2+88m+13)/(2mq),&
d&=(128m^2+120m+25)/(2mq),\\
e&=(64m^2+68m+16)/(mq),&
h&=(64m^2+52m+8)/(mq).
\end{aligned}$$

They solve the six equations

$$\begin{aligned}
(1+2m)a-2mc&=1,&(1+4m)b-2m(c+h)&=1,\\
3mc-m(a+b+d)&=1,&3md-m(c+h+e)&=1,\\
2m(e-d)&=1,&4mh-2m(b+d)&=1.
\end{aligned}$$

Substitution after multiplication by the common positive denominator
$2m(16m+7)$ is a polynomial identity, proving the formulas for every
$m>0$, not just sampled migration rates. The required contrast is
$e+h-2d=-1/(mq)$. For the explicit unit-rate check,

$$T\big|_{m=1}=\frac1{46}
\begin{pmatrix}168&229&273&296\\229&200&248&273\\
273&248&200&229\\296&273&229&168\end{pmatrix}.$$

Notice that endpoint and interior same-deme means differ:
$a=4-8/q$ and $b=4+8/q$. One cannot collapse these into a single state
or stop at first same-deme contact and add a common coalescence delay.
Peter's discussion supplies the structural motivation; the displayed
finite-rate formula is derived here for the model stated above.

For a population-pattern $D$ interpretation, additionally assume the
model frequencies lie in $[0,1]$ and sample one Bernoulli allele per
population independently conditional on the locus/frequencies. Let
$c_{abcd}$ be the integrated weight of a binary pattern. Expanding its
four Bernoulli factors gives
$f_4=c_{1010}+c_{0101}-c_{0110}-c_{1001}$.
The sum $Z_D$ of these four nonnegative pattern weights is finite and
at least $|f_4|>0$. Hence their normalized signed contrast $f_4/Z_D$
is nonzero (the opposite ABBA-minus-BABA orientation changes its sign).
This is a ratio of population pattern weights, not a claim that a
finite-sample ratio is unbiased.

The pair-time calculation alone does not construct allele frequencies
or a mutation/sampling model satisfying the coalescent model's
heterozygosity relation. That instantiation remains a separate bridge;
the $f_4$ and pattern interpretations above state their assumptions
rather than assuming this construction was supplied by the pair chain.

## Sources

- B. M. Peter, "Admixture, Population Structure, and F-Statistics", *Genetics* 202(4) (2016), 1485–1501, <https://doi.org/10.1534/genetics.115.183913>, Equations 24a–c, the "Stepping-stone models" discussion around Equation 35, and Discussion; full text <https://pmc.ncbi.nlm.nih.gov/articles/PMC4905545/>. The paper motivates the distinction between persistent structure and a pulse. The six-class finite-rate calculation here is not attributed to its same-deme-collapsed calculation.
