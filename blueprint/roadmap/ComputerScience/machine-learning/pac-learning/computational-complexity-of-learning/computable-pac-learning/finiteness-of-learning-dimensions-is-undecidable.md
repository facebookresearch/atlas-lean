# Finiteness of complexity measures of computable function classes is undecidable

Given a computable description of a binary-valued function class, no algorithm decides whether the class has finite VC dimension, finite teaching dimension or finite Littlestone dimension, or whether it has an infinite Littlestone tree; so PAC, exact and online learnability are undecidable from such descriptions.

**Setting (Caro).** A class $\mathcal{G}$ of functions $\mathbb{N} \to \mathbb{N}$ is *computable* if there is a total computable $G : \mathbb{N} \times \mathbb{N} \to \mathbb{N}$ with $\mathcal{G} = \{ n \mapsto G(m, n) : m \in \mathbb{N} \}$; a code of $G$ for a fixed universal machine serves as a description of $\mathcal{G}$. Let $c_c(\{0,1\})$ be the set of $\{0,1\}$-valued sequences with finite support. For a Turing machine $M$ and $a \in c_c(\{0,1\})$, let $h_a(n) = a(n)$ if $M$ does not halt within $n$ steps on the empty input and $h_a(n) = 0$ otherwise, and let $\mathcal{H}_M = \{ h_a : a \in c_c(\{0,1\}) \}$. For a class $\mathcal{G} \subseteq \{0,1\}^{\mathbb{N}}$, the *VC dimension* is the largest size of a finite set on which $\mathcal{G}$ realizes all labelings; the *teaching dimension* is the supremum over $g \in \mathcal{G}$ of the least size of a set of labeled points consistent with $g$ and with no other member of $\mathcal{G}$; a *Littlestone tree* is a complete binary tree of points such that every branch, with its left and right turns read as labels, is realized by some member of $\mathcal{G}$, and the *Littlestone dimension* is the largest depth of a finite Littlestone tree.

**Theorem (Caro).** There is no Turing machine that, given the code of a computable class from the family $\{\mathcal{H}_M\}_M$, decides any one of the following:

1. whether the class is finite (equivalently, whether it differs from $c_c(\{0,1\})$);
2. whether it has finite VC dimension;
3. whether it has finite teaching dimension;
4. whether it has finite Littlestone dimension;
5. whether it has an infinite Littlestone tree.

By the characterizations of PAC learnability for binary classification by finite VC dimension, of uniform online learnability by finite Littlestone dimension, and of universal online learnability by the absence of infinite Littlestone trees, the source concludes that these forms of learnability are undecidable from computable descriptions. The source also proves the analogous independence results relative to a consistent formal system.

## Depends on

None.

## Proof depends on

- [Halting is undecidable](../../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

If $M$ halts on the empty input after $N$ steps, every $h_a$ vanishes beyond $N$, so $\mathcal{H}_M$ is finite and all four measures are finite; if $M$ never halts, $\mathcal{H}_M = c_c(\{0,1\})$, which shatters every finite set, has infinite teaching dimension and has an infinite Littlestone tree. The function $(M, m, n) \mapsto h_{a_m}(n)$, for a computable enumeration $(a_m)$ of $c_c(\{0,1\})$, is computable, so a code of $\mathcal{H}_M$ is computable from $M$. A decision procedure for any of the five properties would therefore decide whether $M$ halts on the empty input.

## Sources

- Matthias C. Caro, *From undecidability of non-triviality and finiteness to undecidability of learnability*, International Journal of Approximate Reasoning 163 (2023), article 109057, https://doi.org/10.1016/j.ijar.2023.109057; the definitions of computable function classes, of $\mathcal{H}_M$, of the teaching dimension and of Littlestone trees, the finiteness corollary of Section 3.2 and the Turing-undecidability corollaries of Section 4, read in arXiv:2106.01382v3. Locators in arXiv:2106.01382v3: Corollaries 3.14, 4.4, 4.13, 4.17 and 4.21.
