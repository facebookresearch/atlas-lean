# Fine numbers

For a natural number $n$, the Fine number $F(n)$, indexed from $0$ so
that $F(0) = 1$, is the rational number

$$F(n) = \frac{1}{n+1} \sum_{i=0}^{n} (-2)^i \, (i+1) \binom{2(n+1)}{n-i}.$$

## Sources

- Milan Janjić, *On Enumeration of Dyck Paths with Colored Hills*, Journal of Integer Sequences 21 (2018), Article
  18.9.7, Section 1 ($\mathbb{F}_1 = 1$) and Section 3 (the explicit formula
  $\mathbb{F}_m = \frac1m \sum_{i=1}^{m} (-2)^{i-1}\, i \binom{2m}{m-i}$); the paper indexes from $1$, so that $F(n) = \mathbb{F}_{n+1}$; <https://cs.uwaterloo.ca/journals/JIS/VOL21/Janjic3/janjic96.tex>.
- The Fine numbers are OEIS A000957.
