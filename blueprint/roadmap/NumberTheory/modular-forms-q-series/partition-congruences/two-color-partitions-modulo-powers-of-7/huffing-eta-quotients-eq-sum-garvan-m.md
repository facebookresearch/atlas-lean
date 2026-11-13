# Huffing identities for three eta quotients

Let
$f_k = \prod_{n \ge 1} (1 - q^{kn})$ in $\mathbb{Q}[[q]]$, let $H$ be the huffing operator
$H\bigl(\sum_n p_n q^n\bigr) = \sum_n p_{7n} q^{7n}$, and let $m_{i,j}$ be Garvan's matrix. For
every $i \ge 1$,

$$H\Bigl(\frac{q^{i+2} f_7^{4i}}{f_1^{4i+1}}\Bigr)
= \sum_{j=1}^{7i+4} m_{4i+1,i+j}\, \frac{q^{7j} f_{49}^{4j-1}}{f_7^{4j}},$$



$$H\Bigl(\frac{q^{i+4} f_7^{4i}}{f_1^{4i+2}}\Bigr)
= \sum_{j=1}^{7i+4} m_{4i+2,i+j}\, \frac{q^{7j} f_{49}^{4j-2}}{f_7^{4j}},$$



$$H\Bigl(\frac{q^{i} f_7^{4i}}{f_1^{4i}}\Bigr)
= \sum_{j=1}^{7i+4} m_{4i,i+j}\, \frac{q^{7j} f_{49}^{4j}}{f_7^{4j}}.$$

These are identities of formal power series over $\mathbb{Q}$. The sums stop at $j = 7i + 4$,
beyond which the coefficients $m$ vanish.

## Sources

- D. S. Gireesh, C. Shivashankar, and B. Hemanthkumar, *On 2-Color Partitions in Which the Parts of One Color Are Restricted to Multiples of 7^k*, INTEGERS 26 (2026), Article A94, Lemma 2.
