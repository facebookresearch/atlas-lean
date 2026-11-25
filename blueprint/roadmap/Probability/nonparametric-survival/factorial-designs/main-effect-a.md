# Main effect of the first factor in a 2×2 design

Factors $A$ and $B$ have levels $0$ and $1$, and cell $c \in \{0,1,2,3\}$ is the treatment combination $(a, b)$ with $c = 2a + b$, so the cells are $(0,0), (0,1), (1,0), (1,1)$. For cell means $m_{ab}$ of the combinations $(a,b)$, the main effect of $A$ is

$$\mathrm{ME}_A = \frac{m_{11} + m_{10} - m_{01} - m_{00}}{2},$$

the average of the two $A = 1$ cell means minus the average of the two $A = 0$ cell means.

## Sources

- T. Dasgupta, N. S. Pillai and D. B. Rubin, "Causal inference from $2^K$ factorial designs using the potential outcomes model", arXiv:1211.2481, Section 3.1, equations (1) and (2).
