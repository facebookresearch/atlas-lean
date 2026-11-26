# Conformal sums of elementary vectors in polyhedral cones

**Definitions.** For $x \in \mathbb{R}^r$ let $\operatorname{supp}(x) = \{i : x_i \neq 0\}$ and $\operatorname{sign}(x) \in \{-,0,+\}^r$; write $\operatorname{sign}(x') \le \operatorname{sign}(x)$ when $x'_i \neq 0$ implies $\operatorname{sign}(x'_i) = \operatorname{sign}(x_i)$. A sum $x = \sum_{e \in E} e$ is **conformal** if $\operatorname{sign}(e) \le \operatorname{sign}(x)$ for every $e \in E$ (no cancellations). In a convex cone $C$, a nonzero $x$ is
- *support-minimal* (SM) if every nonzero $x' \in C$ with $\operatorname{supp}(x') \subseteq \operatorname{supp}(x)$ has $\operatorname{supp}(x') = \operatorname{supp}(x)$;
- *conformally non-decomposable* (cND) if $x = x_1 + x_2$ with nonzero $x_1, x_2 \in C$ and $\operatorname{sign}(x_1), \operatorname{sign}(x_2) \le \operatorname{sign}(x)$ forces $x_1 = \lambda x_2$ for some $\lambda > 0$.

For a linear subspace $S \subseteq \mathbb{R}^r$ and $0 \le d \le r$, the **s-cone** is $C(S,d) = \{(x, y) \in \mathbb{R}^{r-d} \times \mathbb{R}^d : (x,y) \in S,\ y \ge 0\}$. The steady-state flux cone $\{f : Nf = 0,\ f_i \ge 0 \text{ for irreversible } i\}$ of a metabolic network with stoichiometric matrix $N$ is an s-cone with $S = \ker N$, and its SM vectors are the elementary flux modes. The **elementary vectors** of an s-cone are its SM vectors; those of a general polyhedral cone $C = \{x : Ax \ge 0\}$ are its cND vectors.

**Theorem.**
1. *(s-cones.)* Every nonzero $x \in C(S,d)$ is a conformal sum of elementary vectors, $x = \sum_{e \in E} e$ with $\operatorname{sign}(e) \le \operatorname{sign}(x)$, where $E$ can be chosen linearly independent with $|E| \le \dim S$ and $|E| \le |\operatorname{supp}(x)|$. In an s-cone, support-minimality, support-wise non-decomposability and conformal non-decomposability coincide, and two SM vectors with the same sign vector are positive multiples of each other; hence there are finitely many elementary vectors up to positive scaling.
2. *(Polyhedral cones.)* Every nonzero $x \in C = \{x : Ax \ge 0\}$ is a conformal sum of cND vectors of $C$, with $|E| \le \dim C$ and $|E| \le |\operatorname{supp}(x)| + |\operatorname{supp}(Ax)|$; $C$ has finitely many cND vectors up to positive scaling.
3. *(Orthant characterization.)* For $x$ in a closed orthant $O$, $x$ is cND in $C$ if and only if $x$ spans an extreme ray of $C \cap O$.

## Expansion

For s-cones the proof is induction on $|\operatorname{supp}(x)|$ with one exchange step: if $x' \in C(S,d)$ is not proportional to $x$ and $\operatorname{supp}(x') \subseteq \operatorname{supp}(x)$, then moving along $x - \lambda x'$ to the first coordinate that vanishes gives a nonzero vector of the cone with $\operatorname{sign} \le \operatorname{sign}(x)$ and strictly smaller support; repeating peels off SM vectors without cancellation. A general cone $\{Ax \ge 0\}$ is lifted to the s-cone $\{(x, Ax) : x \in C\}$, whose cND vectors correspond one to one with those of $C$. This refines the Minkowski and Carathéodory theorems: an elementary vector need not be extreme (in the cone $\{3x_1 + x_2 \ge 0,\ -x_1 + x_2 \ge 0\}$ the positive $x_2$-axis is elementary but not an extreme ray). In metabolic pathway analysis the theorem guarantees that every steady-state flux splits into elementary modes in which no reversible reaction runs backwards relative to the total flux.

## Sources

- S. Müller, G. Regensburger, "Elementary vectors and conformal sums in polyhedral geometry and their relevance for metabolic pathway analysis", Frontiers in Genetics 7 (2016) 90, Section 2 (definitions SM, swND, cND, EX), Section 3.1 (Definition 1, Lemma 2, Theorem 3, Propositions 4–5), Section 3.2 (Definition 6, Lemma 7, Theorem 8, Propositions 9–10), Section 3.5 (Example 2), <https://doi.org/10.3389/fgene.2016.00090>, PMCID: PMC4877377.
