# Jain's fairness index

For an allocation $x = (x_1, \dots, x_n)$ of a resource among $n \ge 1$ users, with $x_i \ge 0$ not all zero, *Jain's fairness index* is

$$
F(x) = \frac{\left( \sum_{i=1}^n x_i \right)^2}{n \sum_{i=1}^n x_i^2} .
$$

It measures how far the allocation is from giving every user the same share; users sharing one bottleneck are treated fairly when all $x_i$ are equal. The declaration is defined for every $n \in \mathbb{N}$ and every real load vector, with real division ($a/0 = 0$): it takes the value $0$ when $n = 0$ or every load is $0$, and equals the displayed formula on nonnegative loads that are not all zero.

## Sources

- D.-M. Chiu and R. Jain, "Analysis of the increase and decrease algorithms for congestion avoidance in computer networks", *Computer Networks and ISDN Systems* 17(1):1–14, 1989, Section 1.4, criterion (2) (fairness).
