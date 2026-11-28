# Segregation ratio under complete ascertainment with sibships of different sizes

For sibships of one common size the consistency of the singles-method estimator is [the consistency of the Li–Mantel estimator](li-mantel-tendsto-ae.md); this page states it for sibships of different sizes. Sibships are ascertained through at least one affected child (complete, or truncate, ascertainment), and each child is affected independently with probability $p \in (0, 1)$. With $T$ the total number of children, $A$ the total number of affected children and $A_1$ the number of sibships with exactly one affected child, all over the ascertained sibships, the singles-method estimate of the segregation ratio is

$$\hat p = \frac{A - A_1}{T - A_1}$$

(Li and Mantel 1968). It is consistent (Li and Mantel 1968; see Gail 1999): in a sibship of size $s$ the number $a$ of affected children is zero-truncated binomial, with $E[a] = sp/(1 - q^s)$ and $P(a = 1) = s p q^{s-1}/(1 - q^s)$, $q = 1 - p$, so that

$$E[a] - P(a = 1) = \frac{sp(1 - q^{s-1})}{1 - q^s} = p\,\bigl(s - P(a = 1)\bigr)$$

for every $s$. Summing over independent ascertained sibships and applying the strong law of large numbers to numerator and denominator gives $\hat p \to p$ almost surely as the number of sibships grows, whatever the mix of sibship sizes, provided the sizes are bounded and sizes $s \ge 2$ occur with positive limiting frequency.

## Depends on

- [Consistency of the Li–Mantel estimator](li-mantel-tendsto-ae.md)
- [The zero-truncated binomial law and its mean](trunc-binom-law-mean.md)

## Expansion

1. The model: independent sibships, independent affection status of children, and complete ascertainment; the zero-truncated binomial law.
2. The identity $E[a - \mathbf 1\{a = 1\}] = p\, E[s - \mathbf 1\{a = 1\}]$, sibship by sibship.
3. Consistency of the ratio estimator by the strong law of large numbers, with the stated conditions on the sibship sizes.
4. The variance estimate $\frac{T - A}{(T - A_1)^3}\bigl(A - A_1 + 2A_2 \frac{T - A}{T - A_1}\bigr)$ of Li and Mantel, with $A_2$ the number of sibships with exactly two affected, and the resulting chi-square test against $p = 1/4$, as separate statements.
5. Incomplete (single and multiple) ascertainment, under which the estimator changes (Davie 1979), as separate statements.

## Sources

- Original result: C. C. Li and N. Mantel, A simple method of estimating the segregation ratio under complete ascertainment, Amer. J. Hum. Genet. 20 (1968), 61–81.
- A. M. Davie, The 'singles' method for segregation analysis under incomplete ascertainment, Ann. Hum. Genet. 42 (1979), 507–512. <https://doi.org/10.1111/j.1469-1809.1979.tb00683.x>
- M. H. Gail, Some of Nathan Mantel's contributions to epidemiology, Stat. Med. 18 (1999), 3389–3400, account of the Li–Mantel estimator, its consistency under truncated binomial sampling and its variance formula.
