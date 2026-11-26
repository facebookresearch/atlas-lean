# Fundamental theorem of natural selection with mutations

**Model.** Partition a population into classes $P_1, \dots, P_N \ge 0$ (not all zero) whose members share birth rate $b_i \ge 0$, death rate $d_i \ge 0$ and Malthusian fitness $m_i = b_i - d_i$. A birth to a parent in class $j$ produces an offspring in class $i$ with probability $f_{ij} \ge 0$, $\sum_i f_{ij} = 1$. Then

$$\frac{dP_i}{dt} = \sum_{j} b_j f_{ij} P_j - d_i P_i, \qquad i = 1, \dots, N .$$

Without mutation ($f_{ij} = \delta_{ij}$) this reduces to independent exponential growth $P_i' = m_i P_i$.

**Theorem.** With $|P| = \sum_i P_i$, mean fitness $\bar m = \sum_i P_i m_i / |P|$ and variance $\mathrm{Var}(m) = \sum_i P_i (m_i - \bar m)^2 / |P|$,

$$\frac{d\bar m}{dt} = \mathrm{Var}(m) + \frac{1}{|P|} \sum_{i} \Bigl( B_i^{\mathrm{in}} - B_i^{\mathrm{out}} \Bigr) (m_i - \bar m), \qquad B_i^{\mathrm{in}} = \sum_j b_j f_{ij} P_j, \quad B_i^{\mathrm{out}} = b_i P_i,$$

where $B_i^{\mathrm{in}}$ is the rate at which individuals are born into class $i$ and $B_i^{\mathrm{out}}$ the rate at which members of class $i$ give birth. With $f_{ij} = \delta_{ij}$ the second term vanishes and $\bar m' = \mathrm{Var}(m)$, Fisher's fundamental theorem in its Malthusian form. The mutational term is the covariance between net birth flux into a class and the class's fitness deviation; it is negative when mutation moves births toward below-average classes, and then mean fitness can decrease even though $\mathrm{Var}(m) \ge 0$.

**Long-term behaviour.** Writing $W = (w_{ij})$ with $w_{ij} = b_j f_{ij} - d_i \delta_{ij}$, the system is $P' = WP$. $W$ has non-negative off-diagonal entries, so when it is irreducible the Perron–Frobenius theorem gives a simple real dominant eigenvalue $\lambda$ with a positive eigenvector $v$; the composition $P(t)/|P(t)|$ converges to $v/|v|$, and $\bar m(t)$ converges to $\lambda$, the long-run growth rate of the population.

## Depends on

- [Fisher's fundamental theorem of natural selection](../../natural-selection-fisher-s-theorem-and-the-price/mean-fitness-select-sub.md)

## Proof depends on

- [Perron–Frobenius theorem for irreducible nonnegative matrices](../../../../LinearAlgebra/special-matrices/perron-frobenius-theorem/perron-frobenius.md)

## Expansion

By the quotient rule, $\bar m' = \sum_i P_i' (m_i - \bar m) / |P|$. Substituting $P_i' = B_i^{\mathrm{in}} - d_i P_i$ and $-d_i = m_i - b_i$ gives $P_i' = (B_i^{\mathrm{in}} - B_i^{\mathrm{out}}) + m_i P_i$; the second piece contributes $\sum_i P_i m_i (m_i - \bar m)/|P| = \mathrm{Var}(m)$ since $\sum_i P_i (m_i - \bar m) = 0$. For the limit, $\bar m = \mathbf{1}^\top \mathrm{diag}(m) P / |P|$ and $\mathbf{1}^\top W = (m_j)_j^\top$ (because $\sum_i f_{ij} = 1$), so $\bar m = \mathbf{1}^\top W P / \mathbf{1}^\top P = |P|'/|P|$, which tends to $\lambda$ as $P$ aligns with $v$. When $f_{ij}$ depends only on $m_i - m_j$ and is skewed toward deleterious effects, as measured mutational distributions are, the mutational term can outweigh the variance, so a continuous supply of mutations does not by itself guarantee perpetual fitness increase. The paper's numerical results on that question concern finite populations, obtained by deleting classes whose size falls below one individual.

## Sources

- W. F. Basener, J. C. Sanford, "The fundamental theorem of natural selection with mutations", Journal of Mathematical Biology 76 (2018) 1589–1622, Section 3 (Equations (3.1)–(3.9), Theorem 2, analytic solutions), <https://doi.org/10.1007/s00285-017-1190-x> (PMC5906570).
