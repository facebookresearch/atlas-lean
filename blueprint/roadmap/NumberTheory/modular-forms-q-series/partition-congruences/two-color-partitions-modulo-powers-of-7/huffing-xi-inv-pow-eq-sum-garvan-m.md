# Garvan's huffing identities for powers of $\xi$

Let
$f_k = \prod_{n \ge 1} (1 - q^{kn})$ in $\mathbb{Q}[[q]]$, let $H$ be the huffing operator
$H\bigl(\sum_n p_n q^n\bigr) = \sum_n p_{7n} q^{7n}$, and let $m_{i,j}$ be Garvan's matrix. Write
$\xi^{-a} = q^{2a} f_{49}^a / f_1^a$ and $T^{-b} = q^{7b} f_{49}^{4b} / f_7^{4b}$ for the
negative powers of $\xi = f_1 / (q^2 f_{49})$ and $T = f_7^4 / (q^7 f_{49}^4)$, which are formal
power series. For every $i \ge 1$,

$$H(\xi^{-i}) = \sum_{j=1}^{2i} m_{i,j}\, T^{-j}$$

and

$$H(\xi^{-4i}) = \sum_{j=1}^{7i} m_{4i,i+j}\, T^{-i-j}.$$

These are identities of formal power series over $\mathbb{Q}$. The sums stop at $j = 2i$,
resp. $j = 7i$, beyond which the coefficients $m$ vanish.

## Sources

- D. S. Gireesh, C. Shivashankar, and B. Hemanthkumar, *On 2-Color Partitions in Which the Parts of One Color Are Restricted to Multiples of 7^k*, INTEGERS 26 (2026), Article A94, Lemma 1.
