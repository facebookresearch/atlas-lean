# A heterozygosity-retention threshold depends on loss tolerance and horizon

Take the neutral Wright-Fisher chain with an integer $M\ge2$ gene copies
and fixed initial count $i$ with $0<i<M$. Let
$H(j)=2(j/M)(1-j/M)$, so $H(i)>0$. For an integer horizon $T\ge1$ and
$0<\delta<1$, the [geometric-decay identity](../population-genetics/wright-fisher-markov-chain/sum-mat-pow-mul-heterozygosity.md)
gives

$$\frac{\mathbb E_i H(X_T)}{H(i)}=(1-1/M)^T.$$

Therefore retention of at least $1-\delta$ of the initial heterozygosity in
expectation is equivalent to

$$M\ge A(T,\delta):=\frac{1}{1-(1-\delta)^{1/T}}.$$

For integer copy counts the least allowed count is $\lceil A(T,\delta)\rceil$.
The statement is about expected heterozygosity, not the probability of
retaining every allele. A monomorphic initial state has $H(i)=0$, so its
retention ratio is undefined; at $T=0$ the ratio is one and this positive-
horizon threshold formula is not used.

For fixed $\delta$, as $T\to\infty$ through positive integers,

$$\frac{A(T,\delta)}{T}\longrightarrow
 \frac{1}{\log(1/(1-\delta))}.$$

For $\delta=0.1$ the coefficient is approximately $9.49122$.
For fixed positive $T$, $A(T,\delta)\sim T/\delta$ as $\delta\downarrow0$.
Here $M$ counts gene copies, not diploid individuals: under an exact diploid
model with $M=2N$, the threshold for integer $N$ is
$\lceil A(T,\delta)/2\rceil$. This criterion yields no universal
horizon-independent 50/500-style population-size rule.

## Depends on

- [Heterozygosity of a Wright-Fisher state](../population-genetics/wright-fisher-markov-chain/heterozygosity.md)

## Proof depends on

- [Geometric decay of heterozygosity](../population-genetics/wright-fisher-markov-chain/sum-mat-pow-mul-heterozygosity.md)

## Expansion

Divide the decay identity by the positive initial heterozygosity, take the
positive $T$th root, and rearrange. Write
$a=\log(1/(1-\delta))>0$; then
$A(T,\delta)=1/(1-e^{-a/T})$, and $1-e^{-u}\sim u$ proves the
large-horizon limit. The small-loss limit follows from
$1-(1-\delta)^{1/T}\sim\delta/T$. Extinction risk, mutation-maintained
variance and demographic viability require different models and criteria.

## Sources

- R. Lande, "Genetics and demography in biological conservation", Science 241 (1988), 1455–1460, <https://doi.org/10.1126/science.3420403>, abstract, for qualitative context only. The exact threshold is derived from the linked Wright-Fisher identity, not attributed to that abstract.
