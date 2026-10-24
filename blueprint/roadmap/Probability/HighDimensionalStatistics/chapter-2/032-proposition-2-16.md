---
article_id: af_4dcf4453354ed92809bf1e75
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: prop_2_16_rademacher_incoherence
---

# Proposition 2.16

Let $\mathbb{X} \in \mathbb{R}^{n \times d}$ be a random matrix with entries $X_{ij}$, $i = 1, \ldots, n$, $j = 1, \ldots, d$ that are i.i.d. Rademacher $(\pm 1)$ random variables. Then, $\mathbb{X}$ has incoherence $k$ with probability $1 - \delta$ as soon as $n \geq 392 k^2 \log(1/\delta) + 784 k^2 \log(d)$. It implies that there exist matrices that satisfy Assumption $\mathrm{INC}(k)$ for $n \gtrsim k^2 \log(d)$.

## Depends on

- [Assumption INC(k)](../section-2/036-k.md)

## Proof depends on

- [Theorem 1.9 (Hoeffding's inequality)](../section-1/009-hoeffding-s-inequality.md)

## Sources

- [MIT 18.S997 High-Dimensional Statistics (Spring 2015), Chapter 2, Section 2.4](../../../../sources/v1/HighDimensionalStatistics.md)
