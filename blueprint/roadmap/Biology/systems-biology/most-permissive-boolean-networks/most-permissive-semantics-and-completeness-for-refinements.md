# Most permissive semantics of Boolean networks and completeness for refinements

**Most permissive configurations.** Let $f = (f_1, \dots, f_n) : \mathbb{B}^n \to \mathbb{B}^n$ be a Boolean network. A most-permissive configuration is $x \in \{0, \nearrow, \searrow, 1\}^n$, where $\nearrow$ (increasing) and $\searrow$ (decreasing) are dynamic states that may be read as either Boolean value. Its admissible Boolean interpretations are

$$\gamma(x) = \{ z \in \mathbb{B}^n : x_i \in \mathbb{B} \Rightarrow z_i = x_i \}.$$

A component $i$ may change, independently of all others,

- from $0$ or $\searrow$ to $\nearrow$ if $\exists z \in \gamma(x)$ with $f_i(z) = 1$;
- from $1$ or $\nearrow$ to $\searrow$ if $\exists z \in \gamma(x)$ with $f_i(z) = 0$;
- from $\nearrow$ to $1$, and from $\searrow$ to $0$, at any time.

So a component cannot go from $\nearrow$ back to $0$ (or from $\searrow$ to $1$) without passing through the opposite dynamic state. These rules define the most permissive Boolean network (MPBN) transition relation.

**Refinements.** A multivalued network on $M = \{0, 1, \dots, m\}$ is $F : M^n \to \{-1, 0, 1\}^n$ (the successors of $y$ add $F(y)$ to a subset of components, staying in $M^n$). With the binarizations

$$\beta(y) = \{ y' \in \mathbb{B}^n : y_i = 0 \Rightarrow y'_i = 0,\ y_i = m \Rightarrow y'_i = 1 \},$$

$F$ **refines** $f$ if for all $y$ and $i$: $F_i(y) < 0$ implies $f_i(y') = 0$ for some $y' \in \beta(y)$, and $F_i(y) > 0$ implies $f_i(y') = 1$ for some $y' \in \beta(y)$. The same definition applies to ODE systems $F : \mathbb{R}_{\ge 0}^n \to \mathbb{R}^n$, with $\beta$ defined by the sign structure and no upper bound $m$.

**Theorem (completeness).** If a refinement $F$ of $f$ has an asynchronous trajectory from $y$ to $y''$, then from every most-permissive configuration $\hat y$ compatible with $y$ ($\hat y_i = 0$ if $y_i = 0$, $\hat y_i = 1$ if $y_i = m$, $\hat y_i \in \{\nearrow, \searrow\}$ otherwise) there is an MPBN trajectory to a configuration $\hat y''$ compatible with $y''$ and consistent with the direction of change ($\hat y''_i = \nearrow$ if $y_i < y''_i < m$, $\hat y''_i = \searrow$ if $0 < y''_i < y_i$, $\hat y''_i = \hat y_i$ if $y''_i = y_i$). The property extends to ODE refinements. Hence if the MPBN excludes a behaviour, no multivalued or quantitative model obeying the same logic can show it.

**Theorem (tightness).** Conversely, if there is an MPBN trajectory between two Boolean configurations, then some multivalued refinement of $f$ has an asynchronous trajectory between matching configurations. So MPBN reachability is the tightest Boolean over-approximation of the reachability of all refinements; the usual synchronous and asynchronous semantics are incomplete in this sense.

## Expansion

Completeness is proved by following the refined trajectory and mapping each intermediate value strictly between $0$ and $m$ to a dynamic state: an increase of component $i$ in $F$ requires a binarization of the current state where $f_i = 1$, which is exactly an admissible interpretation in which the corresponding most-permissive transition is enabled. Only signs of $F$ are used, which is why ODE refinements are covered. The motivating example is the incoherent feed-forward loop where node $1$ activates node $2$, and node $3$ requires $2$ active and $1$ inactive: a refinement in which an intermediate level of $2$ already activates $3$ before $1$ reaches its inhibition threshold shows transient activation of all three nodes, which neither synchronous nor asynchronous Boolean dynamics reach from the all-zero state, while the MPBN does (component $3$ turns $\nearrow$ while $1$ is still $\nearrow$ and read as $0$).

## Sources

- L. Paulevé, J. Kolčák, T. Chatain, S. Haar, "Reconciling qualitative, abstract, and scalable modeling of biological networks", Nature Communications 11 (2020), 4256, Results ("Incompleteness of (a)synchronous BNs", "The Most Permissive execution paradigm for BNs", Fig. 3, "Formal guarantees for model refinements", Eqs. (4)–(6)) and Supplementary Note 2 (Theorem 1, Corollary 1, Theorem 2), <https://doi.org/10.1038/s41467-020-18112-5> (PMC7450094).
