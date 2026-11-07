# Mutually Latin profiles with $k$ soulmate pairs

Let $n$ and $k$ be natural numbers and
let $L_n$ be the number of Latin squares of order $n$. Call the men's preferences of a preference
profile for $n$ men and $n$ women Latin when, for every position $r$, distinct men rank distinct
women at position $r$, and likewise for the women's preferences. The number of preference
profiles whose men's and women's preferences are both Latin and that have exactly $k$ soulmate
pairs is

$$\frac{L_n^2}{n!} \binom{n}{k} \sum_{i=0}^{n-k} \frac{(-1)^i (n-k)!}{i!}.$$

When $k > n$ the binomial coefficient vanishes and both sides are $0$.

## Sources

- Borodin et al., *Sequences of the Stable Matching Problem*, Journal of Integer Sequences 27 (2024), Article 24.2.2, Theorem 9 (`jis-2024-24.2.2-thm-9`).
