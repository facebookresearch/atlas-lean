# Heterosis from among-population allele-frequency variance

At a biallelic locus, assign viability values $1,1-hs,1-s$ to $AA,Aa,aa$,
with $0\le s\le1$ and $0\le h\le1$. Let a population's $a$ frequency
$Q\in[0,1]$ be random with mean $\mu$ and variance $V$.
Compare two sampling rules for a zygote: two independent gametes from the
same sampled population, or one gamete from each of two populations
whose frequencies $Q_1,Q_2$ are independent with that same law.
The expected-viability advantage of the second rule is exactly

$$\mathbb E W_{\rm cross}-\mathbb E W_{\rm within}=s(1-2h)V.$$

For $s>0$, it is positive exactly when $h<1/2$ and $V>0$, zero when
$h=1/2$ or $V=0$, and negative for $h>1/2$ and $V>0$.
This is a one-generation offspring-viability comparison, not a theorem
about demographic persistence, long-term rescue or local adaptation.

## Expansion

The within-population homozygous-$a$ probability is $\mathbb E Q^2$ and
the heterozygote probability is $2(\mu-\mathbb E Q^2)$.
For independent cross populations they are $\mu^2$ and $2\mu(1-\mu)$.
Thus the respective means are
$1-2hs(\mu-\mathbb E Q^2)-s\mathbb E Q^2$ and
$1-2hs(\mu-\mu^2)-s\mu^2$. Subtract and use
$V=\mathbb E Q^2-\mu^2$.
Independence matters: with equal marginals but covariance $C$ between the
two cross-population frequencies, the same subtraction gives
$s(1-2h)(V-C)$. In particular choosing the same frequency twice gives no
advantage even if $V>0$.

## Sources

- M. C. Whitlock, P. K. Ingvarsson and T. Hatfield, "Local drift load and the heterosis of interconnected populations", Heredity 84 (2000), 452--457, <https://doi.org/10.1046/j.1365-2540.2000.00693.x>, abstract, for the Wright-distribution analysis of partially recessive deleterious alleles and heterosis. The iid-population identity above is derived directly; the source's parameter-dependent stationary-distribution conclusions are not assumed here.
