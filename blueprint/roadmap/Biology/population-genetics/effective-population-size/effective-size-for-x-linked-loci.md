# Effective size for an X-linked locus

Consider a dioecious population with $N_f$ females and $N_m$ males in every generation, at an X-linked neutral locus. A daughter
receives a uniformly chosen X of a uniformly chosen mother and the X of a uniformly chosen father; a son receives a uniformly
chosen X of a uniformly chosen mother; all choices are independent. Let $h_A, h_B, h_C, h_D$ be the probabilities that two distinct
X copies are not identical by descent when they are, respectively, the two copies in one female, copies in two different
females, one copy in a female and one in a male, and copies in two different males. Conditioning on the parents shows that
$(h_A, h_B, h_C, h_D)$ evolves by a linear map whose limit as $N_f, N_m \to \infty$ has leading eigenvalue $1$, with right eigenvector
$(1, 1, 1, 1)$ and left eigenvector $(0, 4, 4, 1)$. First-order perturbation in $1/N_f$ and $1/N_m$ gives the leading eigenvalue

$$\lambda = 1 - \frac19\Bigl(\frac{2}{N_f} + \frac{1}{N_m}\Bigr) + O\bigl(N_f^{-2} + N_m^{-2}\bigr),$$

so the [eigenvalue effective size](effective-population-size-definitions.md) is

$$N_e = \frac{1}{2(1 - \lambda)} = \frac{9 N_f N_m}{4 N_m + 2 N_f}\,(1 + o(1)) .$$

With equal numbers, $N_f = N_m = N/2$, this is $\frac34 N$, the size of a population with as many X copies, $\frac32 N$, as the actual one.

## Depends on

- [Inbreeding, variance and eigenvalue effective population sizes](effective-population-size-definitions.md)

## Related topics

- [Effective population size with separate sexes](effective-size-with-separate-sexes.md)

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics*, University of Washington (2019 edition), <https://felsenst.github.io/pgbook/pgbook.pdf>, Section VI.6 (the recursion method with non-identity probabilities within and between individuals). The X-linked recursion and its eigenvalue are derived above.
