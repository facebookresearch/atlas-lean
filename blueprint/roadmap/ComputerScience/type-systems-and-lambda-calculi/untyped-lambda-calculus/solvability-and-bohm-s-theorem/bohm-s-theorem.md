# Böhm's theorem

Write $\mathbf{0} = \lambda x y.\, y$ and $\mathbf{1} = \lambda x y.\, x$. Let $t$ and $t'$ be closed β-normal λ-terms that are not βη-convertible. Then there are closed
terms $t_1, \dots, t_k$ such that

$$t\, t_1 \cdots t_k \simeq_\beta \mathbf{0} \quad\text{and}\quad t'\, t_1 \cdots t_k \simeq_\beta \mathbf{1}.$$

Consequently, for arbitrary terms $v$ and $v'$ there are terms $t_1, \dots, t_k$ with $t\, t_1 \cdots t_k \simeq_\beta v$ and $t'\, t_1 \cdots t_k \simeq_\beta v'$.

## Depends on

- [Beta equivalence in the untyped term model](../../system-f/the-existing-untyped-beta-conversion-term-model/beta-eq.md)
- [Named, de Bruijn and locally nameless lambda terms](../../syntax-with-binders/named-de-bruijn-and-locally-nameless-lambda-terms.md)
- [η-reduction and βη-conversion](../beta-reduction-and-confluence/eta-reduction-and-beta-eta-conversion.md)

## Proof depends on

- [Böhm separation with applicators](bohm-separation-with-applicators.md)
- [Church–Rosser theorem for βη-reduction](../beta-reduction-and-confluence/church-rosser-theorem-for-beta-eta-reduction.md)

## Sources

- J.-L. Krivine, *Lambda-Calculus, Types and Models*, translated from the French by R. Cori, revised online edition, 2011, <https://www.irif.fr/~krivine/articles/Lambda.pdf>: Chapter 5, Theorem 5.2 (Böhm) and Corollary 5.3, proved through Theorem 5.6 (separation by Böhm transformations after substituting applicators $\alpha_n = \lambda z_1 \dots z_n z.\, z\, z_1 \cdots z_n$) and Lemma 5.5.
