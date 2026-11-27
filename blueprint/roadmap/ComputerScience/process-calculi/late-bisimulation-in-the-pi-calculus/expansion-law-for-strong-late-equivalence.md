# Expansion law for strong late equivalence

Let $P = \sum_i \alpha_i . P_i$ and $Q = \sum_j \beta_j . Q_j$, where no $\alpha_i$ binds a name free in $Q$ and no $\beta_j$ binds a name free in $P$. Then, for [strong late equivalence](strong-late-equivalence.md),

$$P \mid Q \sim \sum_i \alpha_i . (P_i \mid Q) + \sum_j \beta_j . (P \mid Q_j) + \sum_{\alpha_i \text{ opp } \beta_j} [x_i = y_j] \tau . R_{ij},$$

where each $\alpha_i$ and $\beta_j$ is a prefix or a derived prefix, $\bar x(u) . R$ standing for $(u) \bar x u . R$ when $x \ne u$, and $\alpha_i$ *opposes* $\beta_j$ in four cases, with $x_i$ and $y_j$ the subjects of $\alpha_i$ and $\beta_j$:

1. $\alpha_i = \bar x_i u$ and $\beta_j = y_j(v)$; then $R_{ij} = P_i \mid Q_j\{u/v\}$;
2. $\alpha_i = \bar x_i(u)$ and $\beta_j = y_j(v)$; then $R_{ij} = (w)(P_i\{w/u\} \mid Q_j\{w/v\})$ for a name $w$ free in neither $(u)P_i$ nor $(v)Q_j$;
3. $\alpha_i = x_i(v)$ and $\beta_j = \bar y_j u$; then $R_{ij} = P_i\{u/v\} \mid Q_j$;
4. $\alpha_i = x_i(v)$ and $\beta_j = \bar y_j(u)$; then $R_{ij} = (w)(P_i\{w/v\} \mid Q_j\{w/u\})$ for a name $w$ free in neither $(v)P_i$ nor $(u)Q_j$.

The matches $[x_i = y_j]$ are needed because $\sim$ is closed under all substitutions, which may identify subjects: for strong late bisimilarity the corresponding [expansion law](expansion-law-for-strong-late-bisimilarity.md) has no matches and lets only actions with the same subject communicate, and that law fails for $\sim$.

## Depends on

- [Strong late equivalence](strong-late-equivalence.md)

## Proof depends on

- [Expansion law for strong late bisimilarity](expansion-law-for-strong-late-bisimilarity.md)
- [Matching laws for strong late bisimilarity](matching-laws-for-strong-late-bisimilarity.md)

## Sources

- R. Milner, J. Parrow and D. Walker, "A calculus of mobile processes, II", *Information and Computation* 100(1):41–77, 1992, <https://www.pure.ed.ac.uk/ws/files/16426068/A_Calculus_of_Mobile_Processes_II.pdf>: Section 3.3, Theorem 10 (the expansion law for strong bisimilarity), Definition 16 (derived prefixes), and Section 4.1, Theorem 15, proved with Theorems 5(a) and 10, and the remark before it that Theorem 10 fails for strong equivalence, as shown in Section 2.2.
