# Linear closures, linear versions and Lie closures of MG-style codon models

**MG-style codon models.** Let $Q_1,Q_2,Q_3$ be $4\times 4$ nucleotide rate matrices (zero column sums) for the three codon positions and $I$ the $4\times4$ identity. Independent substitution at the three positions gives the $64\times64$ triplet rate matrix

$$
Q_{\mathrm{triplet}}=Q_1\otimes I\otimes I+I\otimes Q_2\otimes I+I\otimes I\otimes Q_3,
$$

which automatically has zero rate for changes requiring two or more nucleotide substitutions. With $G$ the $64\times 64$ matrix carrying $\omega$ for non-synonymous single-nucleotide changes, $1$ for synonymous ones and $0$ for changes to or from stop codons, the **MG-style codon model** is $Q_{\mathrm{codon}}=Q_{\mathrm{triplet}}\circ G$: the entrywise product with diagonal reset to give zero column sums. Taking $Q_1=Q_2=Q_3$ equal to Jukes–Cantor or Kimura two-parameter (K2ST) matrices gives JC-MG (rates $\alpha,\alpha\omega$; two parameters) and K2ST-MG (rates $\alpha,\alpha\omega,\beta,\beta\omega$; three parameters).

**Closures.** For a set $\mathcal A\subseteq\mathrm{Mat}_{n\times m}(\mathbb R)$ defined by polynomial constraints on its entries:

- its **linear closure** is the smallest linear subspace containing $\mathcal A$;
- for $B\in\mathcal A$, the tangent space $T_B(\mathcal A)=\operatorname{span}_{\mathbb R}\{A'(0): A(t)\in\mathcal A\ \forall t,\ A(0)=B\}$ is the **linear version** of $\mathcal A$ at $B$;
- the **Lie closure** of a linear space of square matrices is the smallest linear space containing it and closed under $[A,B]=AB-BA$. A model whose rate matrices form a Lie algebra has multiplicatively closed Markov matrices $e^{Qt}$.

**Lemma.** If $\mathcal A$ is defined by polynomial constraints of positive degree, then (i) $T_B(\mathcal A)$ is a subspace of the linear closure of $\mathcal A$ for every $B\in\mathcal A$; (ii) if all constraints are homogeneous of positive degree, $T_0(\mathcal A)$ equals the linear closure. At $B$ with all entries equal to $1$, the linear version replaces every product in a constraint by a sum and every nonzero constant by $0$ (for example $\alpha\omega\mapsto\alpha+\omega$, so $\omega$ becomes the coefficient of a fixed non-synonymous indicator matrix $G^{*}$).

**Result (Lie closures are impractically large).** The Lie closure of JC-MG (whose linear closure and linear version coincide, a 2-dimensional space) has dimension $1996$. The Lie closure of the linear closure of K2ST-MG (4-dimensional) and the Lie closure of its linear version (3-dimensional) coincide and have dimension $2106$, out of a maximum of $64\cdot 64-64=4032$ free off-diagonal rates. Any non-trivial partial Lie closure of JC-MG of dimension below $227$ (closing up to generation $10$ of nested brackets) contains no non-trivial stochastic matrices, i.e. its extra directions force negative off-diagonal rates. By contrast, linear closures and linear versions stay small: for example HKY-MG ($6$ parameters) has a $6$-parameter linear version and a $16$-parameter linear closure.

## Depends on

- [Codon as a triple of nucleotides](../../../codon-substitution-models-and-dn-ds/codon.md)
- [Codons differing at exactly one position](../../../codon-substitution-models-and-dn-ds/is-single-change.md)

## Expansion

Part (i) of the lemma holds because derivatives of paths in $\mathcal A$ are limits of difference quotients, which lie in any linear space containing $\mathcal A$, and linear spaces are closed. For (ii), homogeneity makes $t\mapsto tC$ a path in $\mathcal A$ through $0$ for every $C\in\mathcal A$, so $C\in T_0(\mathcal A)$. Lie closures are computed by repeatedly adding brackets of basis elements that leave the current span until all brackets lie inside it; for the codon models this stabilizes only at thousands of dimensions, and a randomized check (brackets of random rational combinations of the basis) confirmed closure. A two-state toy version of the construction shows the same effect: small departures from full symmetry of the starting space make the Lie closure nearly as large as possible. Since multiplicative closure cannot be achieved at a usable size, the linear closures and linear versions, which have few parameters and admit positive rates, are proposed as the practical alternative for reducing mis-estimation of $\omega$.

## Sources

- Julia A. Shore, Jeremy G. Sumner, Barbara R. Holland, "The impracticalities of multiplicatively-closed codon models: a retreat to linear alternatives", Journal of Mathematical Biology 81 (2020), 549–573, <https://doi.org/10.1007/s00285-020-01519-5>. Published version of arXiv:1804.11249, cited next; locators there refer to the arXiv version.
- Julia A. Shore, Jeremy G. Sumner and Barbara R. Holland, "The impracticalities of multiplicatively-closed codon models: a retreat to linear alternatives", arXiv (2018): Section 2 (definition of MG-style codon models), Section 3 (definitions of linear closure, tangent space and linear version; the lemma on tangent spaces and linear closures and the lemma on linear versions at the all-ones matrix; the table of linear versions and closures; subsections "Lie closures of codon models" and "Further analysis: partial Lie closures"), Section 4 (toy model). <https://doi.org/10.48550/arXiv.1804.11249>
