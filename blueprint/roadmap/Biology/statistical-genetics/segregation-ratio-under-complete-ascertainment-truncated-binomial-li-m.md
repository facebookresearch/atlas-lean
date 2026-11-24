# Segregation ratio under complete ascertainment

Sibships are ascertained through at least one affected child (complete, or truncate, ascertainment), and each child is affected independently with probability $p \in (0, 1)$. With $T$ the total number of children, $A$ the total number of affected children and $A_1$ the number of sibships with exactly one affected child, all over the ascertained sibships, the singles-method estimate of the segregation ratio is

$$\hat p = \frac{A - A_1}{T - A_1}$$

(Singles-method notes, Section 5.7). It is consistent: in a sibship of size $s$ the number $a$ of affected children is zero-truncated binomial, with $E[a] = sp/(1 - q^s)$ and $P(a = 1) = s p q^{s-1}/(1 - q^s)$, $q = 1 - p$, so that

$$E[a] - P(a = 1) = \frac{sp(1 - q^{s-1})}{1 - q^s} = p\,\bigl(s - P(a = 1)\bigr)$$

for every $s$. Summing over independent ascertained sibships and applying the strong law of large numbers to numerator and denominator gives $\hat p \to p$ almost surely as the number of sibships grows, whatever the mix of sibship sizes, provided the sizes are bounded and sizes $s \ge 2$ occur with positive limiting frequency.

## Expansion

1. The model: independent sibships, independent affection status of children, and complete ascertainment; the zero-truncated binomial law.
2. The identity $E[a - \mathbf 1\{a = 1\}] = p\, E[s - \mathbf 1\{a = 1\}]$, sibship by sibship.
3. Consistency of the ratio estimator by the strong law of large numbers, with the stated conditions on the sibship sizes.
4. The variance estimate $\frac{T - A}{(T - A_1)^3}\bigl(A - A_1 + 2A_2 \frac{T - A}{T - A_1}\bigr)$ of the notes, with $A_2$ the number of sibships with exactly two affected, and the resulting chi-square test against $p = 1/4$, as separate statements.
5. Single and multiple ascertainment, under which the estimator changes, as separate statements.

## Sources

- Calculation of corrected segregation ratio according to Singles method, Section 5.7 of population genetics course notes, Royal Veterinary and Agricultural University, Copenhagen. <http://www.ihh.kvl.dk/htm/kc/popgen/genetik/applets/single.htm>
