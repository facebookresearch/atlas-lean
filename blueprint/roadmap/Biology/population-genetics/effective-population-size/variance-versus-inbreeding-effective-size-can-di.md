# Variance and inbreeding effective sizes differ when population size changes

In a Wright–Fisher population whose $2N_{t+1}$ gene copies in generation $t + 1$ are drawn independently and uniformly,
with replacement, from the $2N_t$ gene copies of generation $t$:

- given the allele frequency $p_t$, the count in generation $t + 1$ is $\mathrm{Binomial}(2N_{t+1}, p_t)$, so $\operatorname{Var}(p_{t+1} \mid p_t) = p_t(1 - p_t)/(2N_{t+1})$ and the [variance effective size](effective-population-size-definitions.md) of this generation is $N_{t+1}$;
- two distinct copies of generation $t + 1$ are copies of the same gene of generation $t$ with probability $1/(2N_t)$, so $1 - F_{t+1} = (1 - 1/(2N_t))(1 - F_t)$ and the inbreeding effective size is $N_t$, as in the [fluctuating-size recursion](effective-size-under-fluctuating-population-size.md).

For example, growth from $N_t = 10$ to $N_{t+1} = 100$ gives variance effective size $100$ and inbreeding effective size
$10$. When $N_t = N_{t+1} = N$ both equal $N$.

## Depends on

- [Inbreeding, variance and eigenvalue effective population sizes](effective-population-size-definitions.md)

## Proof depends on

- [Effective population size under fluctuating population size](effective-size-under-fluctuating-population-size.md)

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics*, University of Washington (2019 edition), <https://felsenst.github.io/pgbook/pgbook.pdf>, Section VI.6 (inbreeding and variance effective numbers "will sometimes differ"). The example is derived above.
