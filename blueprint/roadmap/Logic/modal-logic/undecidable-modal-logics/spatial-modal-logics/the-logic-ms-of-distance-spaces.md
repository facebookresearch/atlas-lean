# The logic MS of distance spaces

The logic MS speaks about regions of a distance space: its terms are built from region variables and nominals with Boolean operations and distance operators such as "somewhere at distance less than a", and its formulas compare such regions.

**Distance and metric spaces.** A *distance space* is a pair $(\Delta, d)$ of a nonempty set $\Delta$ and a function $d : \Delta \times \Delta \to \mathbb R_{\ge 0}$ with $d(x, y) = 0$ iff $x = y$; it is a *metric space* if moreover $d(x, y) = d(y, x)$ and $d(x, z) \le d(x, y) + d(y, z)$ for all $x, y, z$. A *model* $\mathfrak M = (\mathcal D, p_0^{\mathfrak M}, p_1^{\mathfrak M}, \ldots)$ over a distance space $\mathcal D = (\Delta, d)$ interprets each region variable $p_i$ as a subset of $\Delta$ and each location constant $\ell_i$ as a point of $\Delta$.

**Terms and formulas.** For $a, b \in \mathbb Q_{\ge 0}$ with $a < b$, the terms of MS are

$$
\tau ::= p_i \mid \{\ell_i\} \mid \overline{\tau} \mid \tau_1 \sqcap \tau_2 \mid \exists^{=a}\tau \mid \exists^{<a}\tau \mid \exists^{>a}\tau \mid \exists^{<b}_{>a}\tau ,
$$

where $\overline{\tau}$ is the complement and $\{\ell_i\}$ is interpreted as a singleton. The distance operators are interpreted by

$$
(\exists^{<a}\tau)^{\mathfrak M} = \{x \in \Delta \mid \exists y\, (d(x, y) < a \wedge y \in \tau^{\mathfrak M})\}, \qquad (\exists^{<b}_{>a}\tau)^{\mathfrak M} = \{x \in \Delta \mid \exists y\, (a < d(x, y) < b \wedge y \in \tau^{\mathfrak M})\},
$$

and similarly for $\exists^{=a}$ and $\exists^{>a}$; the duals $\forall^{=a}, \forall^{<a}, \ldots$ are defined as usual. Atomic formulas are $\tau_1 \sqsubseteq \tau_2$, true in $\mathfrak M$ iff $\tau_1^{\mathfrak M} \subseteq \tau_2^{\mathfrak M}$, and formulas are Boolean combinations of atomic formulas. A formula is *satisfiable in a model based on a metric space* if it is true in some model over a metric space.

## Depends on

None.

## Proof depends on

None.

## Expansion

Over metric spaces MS is as expressive as the two-variable fragment of first-order logic with equality, constants, unary predicates for the region variables and binary predicates $d(x, y) < a$ and $d(x, y) = a$, by an effective translation. The operator $\exists^{<b}_{>a}$ (the "doughnut") is not the intersection of $\exists^{<b}$ and $\exists^{>a}$: in general $\exists^{<b}_{>a}\tau \ne \exists^{<b}\tau \sqcap \exists^{>a}\tau$ (Section 3.3 and Figure 1.6 of the survey); the fragment with only $\exists^{\le a}$ and $\exists^{>a}$ behaves much better.

## Sources

- O. Kutz, F. Wolter, H. Sturm, N.-Y. Suzuki and M. Zakharyaschev, "Logics of metric spaces", *ACM Transactions on Computational Logic* 4(2):260–294, 2003, <https://doi.org/10.1145/635499.635504>: the original definition of MS, cited beside the copy read.
- R. Kontchakov, A. Kurucz, F. Wolter and M. Zakharyaschev, "Spatial logic + temporal logic = ?", in *Handbook of Spatial Logics*, Springer, 2007, pp. 497–564, <https://doi.org/10.1007/978-1-4020-5587-4_9>; read in the open-access author copy at <https://kuag19.github.io/homepage/st.pdf>: Section 3.1 (metric and distance spaces) and Section 3.3 (logics of distance spaces, the logic MS).
