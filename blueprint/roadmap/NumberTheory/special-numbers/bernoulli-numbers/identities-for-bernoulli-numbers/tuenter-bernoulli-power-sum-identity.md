# Tuenter's power-sum identity for Bernoulli numbers

Let $a$ and $b$ be nonzero complex
numbers and let $n \ge 1$ be a natural number with $b^n \ne a^n$. Let $\sigma_x(i) \in \mathbb{C}$,
for $x \in \mathbb{C}$ and $i \in \mathbb{N}$, satisfy
$(i+1)\,\sigma_x(i) = B_{i+1}(x+1) - B_{i+1}$ for all $x$ and $i$, where $B_m(t)$ denotes the
Bernoulli polynomial and $B_m$ the Bernoulli number, with $B_1 = -\tfrac{1}{2}$. Then

$$B_n = \frac{1}{b^n - a^n} \sum_{i=1}^{n} \binom{n}{i} B_{n-i}
\left( a^{n-1-i} \, b^i \, \sigma_{a-1}(i) - a^i \, b^{n-1-i} \, \sigma_{b-1}(i) \right),$$

where the exponents $n - 1 - i$ are integers, equal to $-1$ when $i = n$.

For a natural number $x$ and $i \ge 1$ the relation gives $\sigma_x(i) = 1^i + 2^i + \dots + x^i$.

## Sources

- Jitender Singh, *On an Arithmetic Convolution*, Journal of Integer Sequences 17 (2014), Article 14.6.7, Corollary with equation `eq23`, lines 339–344, identified there as Tuenter's identity at `c = 0`, line 348, <https://cs.uwaterloo.ca/journals/JIS/VOL17/Singh/singh8.tex>.
