# A pca from an s-m-n theorem and a universal function

Let $A$ be a set with a partial binary operation $e \cdot a$. Call a partial function $f : A \rightharpoonup A$ *numbered*, with index $e$, if $f(a) \simeq e \cdot a$ for all $a \in A$. Suppose there is an injective pairing $\langle -, - \rangle : A \times A \to A$ such that (i) *pairing and projections*: there are indices $\mathrm{fst}, \mathrm{snd}$ of the projections, with $\mathrm{fst}\cdot\langle a, b\rangle = a$ and $\mathrm{snd}\cdot\langle a, b\rangle = b$ for all $a, b$, and the numbered functions are closed under composition $x \mapsto f(g(x))$ and under pairing $x \mapsto \langle f(x), g(x)\rangle$ (defined iff both components are); (ii) *s-m-n*: there is $\sigma \in A$ such that for all $e, a \in A$, $\sigma\cdot\langle e, a\rangle$ is defined and $(\sigma\cdot\langle e, a\rangle)\cdot b \simeq e\cdot\langle a, b\rangle$ for all $b$; and (iii) a *universal function*: there is $u \in A$ with $u\cdot\langle e, b\rangle \simeq e\cdot b$ for all $e, b$. Then there are elements $\mathsf{k}, \mathsf{s}$ making $(A, \cdot)$ a partial combinatory algebra.

## Proof sketch

By (ii), $\sigma\cdot\langle \mathrm{snd}, a\rangle$ is an index of the identity and $\sigma\cdot\langle \mathrm{fst}, c\rangle$ an index of the constant function $c$, with $\mathrm{fst}, \mathrm{snd}$ as in (i); so by (i) $a \mapsto \sigma\cdot\langle e, a\rangle$ is numbered for every $e$. Take $\mathsf{k}$ to be an index of $a \mapsto \sigma\cdot\langle \mathrm{fst}, a\rangle$; then $\mathsf{k}\cdot a\cdot b \simeq \mathrm{fst}\cdot\langle a, b\rangle = a$. By (i) and (iii), $g : \langle\langle a,b\rangle, c\rangle \mapsto u\cdot\langle u\cdot\langle a, c\rangle, u\cdot\langle b, c\rangle\rangle \simeq (a\cdot c)\cdot(b\cdot c)$ has an index $g_0$; let $f_0$ be an index of $y \mapsto \sigma\cdot\langle g_0, y\rangle$ and $\mathsf{s}$ an index of $a \mapsto \sigma\cdot\langle f_0, a\rangle$. Then $\mathsf{s}\cdot a\cdot b \simeq f_0\cdot\langle a, b\rangle = \sigma\cdot\langle g_0, \langle a, b\rangle\rangle$ is defined, and $\mathsf{s}\cdot a\cdot b\cdot c \simeq g_0\cdot\langle\langle a, b\rangle, c\rangle \simeq (a\cdot c)\cdot(b\cdot c)$.

## Depends on

- [Partial combinatory algebra](partial-combinatory-algebra.md)
- [Parametrized s-m-n theorem](../../../TheoryOfComputation/computability/exists-computable-code.md)

## Sources

- J. van Oosten, "Realizability: An Introduction to its Categorical Side", Studies in Logic and the Foundations of Mathematics 152, Elsevier, 2008.
- S. C. Kleene, "Introduction to Metamathematics", North-Holland and Van Nostrand, 1952.
