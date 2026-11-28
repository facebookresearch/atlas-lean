# Expansion law for strong late bisimilarity

In the [late transition semantics](late-transition-semantics-of-the-pi-calculus.md), for $x \ne u$ write $\bar x(u) . P$ for $(u) \bar x u . P$ (a *derived prefix*). Let $P = \sum_i \alpha_i . P_i$ and $Q = \sum_j \beta_j . Q_j$, where each $\alpha_i$ and $\beta_j$ is a prefix or a derived prefix, $\mathrm{bn}(\alpha_i) \cap \mathrm{fn}(Q) = \emptyset$ for every $i$ and $\mathrm{bn}(\beta_j) \cap \mathrm{fn}(P) = \emptyset$ for every $j$. Then, for [strong late bisimilarity](strong-late-bisimilarity.md),

$$P \mid Q \mathrel{\dot\sim} \sum_i \alpha_i . (P_i \mid Q) + \sum_j \beta_j . (P \mid Q_j) + \sum_{\alpha_i \text{ comp } \beta_j} \tau . R_{ij},$$

where $\alpha_i$ *complements* $\beta_j$ in four cases, which also define $R_{ij}$:

1. $\alpha_i = \bar x u$ and $\beta_j = x(v)$; then $R_{ij} = P_i \mid Q_j\{u/v\}$;
2. $\alpha_i = \bar x(u)$ and $\beta_j = x(v)$; then $R_{ij} = (w)(P_i\{w/u\} \mid Q_j\{w/v\})$ for a name $w$ free in neither $(u)P_i$ nor $(v)Q_j$;
3. $\alpha_i = x(v)$ and $\beta_j = \bar x u$; then $R_{ij} = P_i\{u/v\} \mid Q_j$;
4. $\alpha_i = x(v)$ and $\beta_j = \bar x(u)$; then $R_{ij} = (w)(P_i\{w/v\} \mid Q_j\{w/u\})$ for a name $w$ free in neither $(v)P_i$ nor $(u)Q_j$.

Only actions with the same subject communicate.

## Depends on

- [Strong late bisimilarity](strong-late-bisimilarity.md)
- [Late transition semantics of the π-calculus](late-transition-semantics-of-the-pi-calculus.md)

## Sources

- R. Milner, J. Parrow and D. Walker, "A calculus of mobile processes, II", *Information and Computation* 100(1):41–77, 1992, <https://www.pure.ed.ac.uk/ws/files/16426068/A_Calculus_of_Mobile_Processes_II.pdf>, Section 3.3: Definition 16 (derived prefixes) and Theorem 10, with the remark after it on the side conditions.
