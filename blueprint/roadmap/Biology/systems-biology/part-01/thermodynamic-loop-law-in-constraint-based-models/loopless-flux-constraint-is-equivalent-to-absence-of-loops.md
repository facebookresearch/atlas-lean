# Loopless flux constraint is equivalent to the absence of internal loops

**Setting.** Let $A = S_{\mathrm{int}} \in \mathbb{R}^{m\times n}$ be the stoichiometric matrix of the $n$ internal reactions of a metabolic network with $m$ metabolites, and $v \in \mathbb{R}^n$ the internal part of a flux distribution. A *loop* is a vector $x \ne 0$ with $Ax = 0$. The flux distribution $v$ *contains a loop* if

$$\exists\, x \in \mathbb{R}^n\setminus\{0\}:\quad Ax = 0\ \text{ and }\ \operatorname{sign}(x_i) \in \{\operatorname{sign}(v_i), 0\}\ \text{ for all } i,$$

that is, some loop runs only through active reactions, in their active directions.

**Sign-pattern alternative.** For every $A \in \mathbb{R}^{m\times n}$ and $d \in \{-1,0,1\}^n$, exactly one of the following holds:

- (a) there is $x \ne 0$ with $Ax = 0$ and $\operatorname{sign}(x_i) \in \{d_i, 0\}$ for all $i$;
- (b) there is $y \in \mathbb{R}^m$ with $\operatorname{sign}\big((A^\top y)_i\big) = d_i$ for every $i$ with $d_i \ne 0$.

**Theorem (soundness and completeness of loopless constraints).** For every $v \in \mathbb{R}^n$ the following are equivalent:

1. $v$ contains no loop;
2. there is $y \in \mathbb{R}^m$ with $\operatorname{sign}\big((A^\top y)_i\big) = -\operatorname{sign}(v_i)$ whenever $v_i \ne 0$;
3. there is $G \in \mathbb{R}^n$ with $N G = 0$, where the rows of $N$ span the null space of $A$, and $\operatorname{sign}(G_i) = -\operatorname{sign}(v_i)$ whenever $v_i \ne 0$.

Hence the mixed-integer loopless constraints remove exactly the flux distributions containing loops and no others. (The trivial flux $v = 0$ satisfies them and must be excluded separately if needed.)

## Expansion

The alternative follows from Gordan's theorem (exactly one of $\exists x \ge 0, x \ne 0, \hat Ax = 0$ and $\exists y, \hat A^\top y > 0$ holds) applied to the matrix $\hat A$ obtained from $A$ by deleting the columns with $d_i = 0$ and negating those with $d_i = -1$. Taking $d = \operatorname{sign}(v)$ and replacing $y$ by $-y$ gives 1 $\Leftrightarrow$ 2. Since the null space of $A$ is the orthogonal complement of the row space, $NG = 0$ iff $G = A^\top y$ for some $y$, giving 2 $\Leftrightarrow$ 3. Thermodynamically, $y$ plays the role of metabolite formation energies and $G = A^\top y$ of reaction Gibbs energies, which must be negative in the direction of positive flux.

## Sources

- Noor E, Lewis NE, Milo R, "A proof for loop-law constraints in stoichiometric metabolic networks", BMC Syst Biol (2012), Gordan's theorem, Corollaries 1–3 and Eqs. (1)–(2), <https://doi.org/10.1186/1752-0509-6-140>, PMCID PMC3560238.
