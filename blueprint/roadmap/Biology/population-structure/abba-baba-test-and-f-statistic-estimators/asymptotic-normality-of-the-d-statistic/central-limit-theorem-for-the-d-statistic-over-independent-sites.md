# Central limit theorem for the D-statistic over independent sites

**Setting.** Four populations $H_1, H_2, H_3, H_4$ are related by the rooted tree $(((H_1, H_2), H_3), H_4)$ with no gene flow. At each of $M$ diallelic sites $i$, let $x_{1i}, \dots, x_{4i} \in [0,1]$ be the (estimated) allele frequencies in the four populations, and set

$$X_i = (x_{1i} - x_{2i})(x_{3i} - x_{4i}), \qquad Y_i = (x_{1i} + x_{2i} - 2x_{1i}x_{2i})(x_{3i} + x_{4i} - 2x_{3i}x_{4i}),$$

so that $|X_i| \le 1$ and $Y_i \ge 0$. The D-statistic is

$$D_M = \frac{\sum_{i=1}^M X_i}{\sum_{i=1}^M Y_i} \in [-1, 1].$$

Assume the sites are independent, frequencies evolve as martingales along the tree, and

1. $v_M := \sum_{i=1}^M \operatorname{Var}(X_i) \to \infty$;
2. $\frac{1}{M}\sum_{i=1}^M \mathbb{E}\,Y_i \to \gamma > 0$;
3. $\frac{1}{M^2}\sum_{i=1}^M \operatorname{Var}(Y_i) \to 0$.

**Theorem.** Each $X_i$ has mean zero, and

$$c_M D_M \xrightarrow{d} \mathcal{N}(0, 1) \qquad (M \to \infty), \qquad c_M = \frac{\gamma M}{\sqrt{v_M}}.$$

Conditions 1–3 hold automatically when the $(X_i, Y_i)$ are i.i.d. with $\operatorname{Var}(X_i) > 0$; the theorem extends the usual $Z$-test for introgression to sites with heterogeneous depth and frequency-estimation error.

## Depends on

Its statement uses only the notions recalled above.

## Proof depends on

- [The unpolarized D-statistic numerator vanishes on a tree](../integral-sample-expect-abba-eq-baba.md)
- [Lindeberg–Feller central limit theorem](../../../../Probability/central-limit-theorems/lindeberg-feller-central-limit-theorem/lindeberg-feller-clt-triangular.md)
- [Slutsky's theorem (ratio form)](../../../../Probability/statistical-estimation/asymptotic-normality-of-maximum-likelihood/div-of-tendsto-in-measure-const.md)

## Expansion

Zero mean: condition on the ancestral frequencies at the internal nodes; given them, $x_{1i} - x_{2i}$ and $x_{3i} - x_{4i}$ are conditionally independent and $\mathbb{E}[x_{1i} - x_{2i} \mid \text{ancestor of } H_1, H_2] = 0$ by the martingale property. For the limit, the Lindeberg condition for $X(M)/\sqrt{v_M}$ follows from $|X_i| \le 1$ and $v_M \to \infty$, giving a standard normal limit; Chebyshev's inequality with condition 3 gives $\frac{1}{M}\sum Y_i \to \gamma$ in probability; Slutsky's theorem combines the two.

## Sources

- S. Soraggi, C. Wiuf and A. Albrechtsen, "Powerful Inference with the D-Statistic on Low-Coverage Whole-Genome Data", *G3: Genes, Genomes, Genetics* (2018), Appendix 1, Theorem 1 (Eq. 8), conditions (9)–(11) and Theorem 5. <https://doi.org/10.1534/g3.117.300192> (PMC5919751)
