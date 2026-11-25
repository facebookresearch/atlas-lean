# Asymptotic law of the Pearson chi-square test of independence

Let an $r \times c$ table of counts $N_{jk}$ ($r, c \ge 2$) be multinomial with $n$ trials and cell probabilities $p_{jk} = a_jb_k$, where $a$ and $b$ are probability vectors with all entries positive. With observed margins $N_{j\cdot}$, $N_{\cdot k}$, let $E_{jk} = N_{j\cdot}N_{\cdot k}/n$ and $X^2 = \sum_{j,k}(N_{jk} - E_{jk})^2/E_{jk}$, with the convention that the terms with $E_{jk} = 0$ are omitted; that event has probability tending to $0$. Then $X^2 \to \chi^2_{(r-1)(c-1)}$ in distribution as $n \to \infty$. The number of degrees of freedom is $rc - 1$ minus the $(r - 1) + (c - 1)$ estimated margin parameters. The goodness-of-fit statistic for fully specified cell probabilities is a separate statement.

## Expansion

A sound expansion specifies the following prerequisites and links their statements.

- Limit law of the Pearson statistic with parameters estimated from the data, for a smooth parametrization of the cell probabilities whose probability-weighted Jacobian is injective and an estimator admitting the efficient linear projection expansion; for the independence table the product-of-margins parametrization with the observed margins is such a case.
- Limit law of the Pearson goodness-of-fit statistic for fully specified cell probabilities, all positive, with at least two cells.

## Sources

- J. Watkins, *Asymptotic evaluations: contingency tables*, lecture slides (chapter 11), University of Arizona, "Degrees of freedom", <https://math.arizona.edu/~jwatkins/J2_contingency.pdf>
