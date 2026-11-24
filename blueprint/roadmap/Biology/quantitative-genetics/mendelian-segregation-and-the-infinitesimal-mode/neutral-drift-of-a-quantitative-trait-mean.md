# Neutral drift of the mean of an additive trait under the infinitesimal model

Consider a monoecious population of $N\ge1$ diploid individuals per generation with Wright–Fisher parent choice: each of the $N$ offspring of generation $t+1$ independently chooses an ordered pair of parents $(f_i,m_i)$, each parent uniform on the $N$ individuals of generation $t$, independently (so selfing has probability $1/N$). Individual $j$ of generation $t$ has additive value $z_j$ and realized pedigree inbreeding coefficient $F_j$. Under the [infinitesimal model](infinitesimal-model-definition.md) with base variance $V_0$, offspring $i$ has

$$z'_i=\frac{z_{f_i}+z_{m_i}}2+R_i,$$

where, given generation $t$ and all parental choices, the segregation residuals $R_1,\ldots,R_N$ are independent, centred, with variances $\tfrac{V_0}2\bigl(1-\tfrac{F_{f_i}+F_{m_i}}2\bigr)$. Write $\bar z_t=\frac1N\sum_jz_j$, $\sigma_t^2=\frac1N\sum_j(z_j-\bar z_t)^2$ for the realized variance of additive values, and $\bar F_t=\frac1N\sum_jF_j$ for the realized mean inbreeding, a random variable. Conditionally on generation $t$:

1. $\mathbb E[\bar z_{t+1}-\bar z_t]=0$;
2. $\displaystyle\operatorname{Var}(\bar z_{t+1}-\bar z_t)=\frac1N\Bigl(\frac{\sigma_t^2}2+\frac{V_0}2\bigl(1-\bar F_t\bigr)\Bigr).$

The conditional independence of residuals across offspring is part of the hypothesis: with a common residual $R_i=R$ of variance $v$, the residual contribution to the variance of $\bar z_{t+1}$ would be $v$ instead of $v/N$.

The closed recursion $1-G_{t+1}=\bigl(1-\frac1{2N}\bigr)(1-G_t)$ holds for the probability $G_t$ that two distinct gene copies of generation $t$, sampled from the $2N$ copies of the gene-copy Wright–Fisher model, are identical by descent; it does not hold for the realized $\bar F_t$. For $N=2$ and unrelated, non-inbred founders, $\bar F_1=0$ exactly when neither offspring is produced by selfing, an event of probability $\tfrac14$, while $\bar F_1>0$ otherwise; so $\bar F_t$ satisfies no deterministic recursion. The relation between $\mathbb E[\bar F_{t+1}]$ and $G_t$, which separates identity within and between individuals, is not asserted here.

## Depends on

- [The infinitesimal model of inheritance](infinitesimal-model-definition.md)

## Proof depends on

- [One-step martingale property of the Wright–Fisher allele count](../../population-genetics/wright-fisher-markov-chain/sum-prob-mul-wright-fisher.md)

## Expansion

A full proof page must establish:

- Part 1, from $\mathbb E[z_{f_i}\mid\text{generation }t]=\bar z_t$ and $\mathbb E[R_i\mid\text{choices}]=0$.
- Part 2, by conditioning on parental choices: the midparent values of distinct offspring are independent with variance $\sigma_t^2/2$; the residuals are uncorrelated with them and with each other; $\mathbb E\bigl[\tfrac12(F_{f_i}+F_{m_i})\bigr]=\bar F_t$.
- The common-residual comparison.
- The gene-copy identity recursion for $G_t$ (the probability that two distinct copies share a parental copy is $1/(2N)$, as in the [geometric decay of heterozygosity](../../population-genetics/wright-fisher-markov-chain/sum-mat-pow-mul-heterozygosity.md)), and the $N=2$ computation for $\bar F_1$ (a selfed offspring of a non-inbred parent has inbreeding $\tfrac12$).
- The relation between $\mathbb E[\bar F_{t+1}]$ and $G_t$, distinguishing within- and between-individual identity.

## Sources

- R. Lande, *Natural selection and random genetic drift in phenotypic evolution*, Evolution (1976).
- J. Felsenstein, *Theoretical Evolutionary Genetics* (GENOME 562 text), University of Washington (2019), <https://felsenst.github.io/pgbook/pgbook.pdf> (quantitative characters and drift; background).
