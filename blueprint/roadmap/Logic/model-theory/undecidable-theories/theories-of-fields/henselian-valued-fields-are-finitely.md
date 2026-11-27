# Henselian valued fields are finitely undecidable

The theory of a nontrivially valued henselian field, in the language of valued fields, is finitely undecidable in equicharacteristic zero, in mixed characteristic, and in equicharacteristic $p$ under separable defectlessness and the Kaplansky condition; consequently every infinite dp-finite field is finitely undecidable.

**Setting.** $\mathcal{L}_{\mathrm{val}}$ is the language of rings with a unary predicate for the valuation ring $\mathcal{O}_v$. A valued field $(K,v)$ is *henselian* if $v$ extends uniquely to every algebraic extension, and *nontrivially valued* if $v$ is not trivial. It is *separably defectless* if $[L:K] = \sum_{w} e(w/v) f(w/v)$ for every finite separable extension $L/K$, the sum over the prolongations $w$ of $v$ to $L$, and, for residue characteristic $p > 0$, *Kaplansky* if the value group $vK$ is $p$-divisible and the residue field $Kv$ is perfect and admits no proper separable algebraic extension of degree divisible by $p$.

**Theorem (Tyrrell).** Let $(K,v)$ be a henselian nontrivially valued field that is

1. of equicharacteristic $0$ (Corollary 4.10), or
2. of mixed characteristic (Theorem 5.3), or
3. of equicharacteristic $p > 0$, separably defectless and Kaplansky (Theorem 5.8).

Then the complete $\mathcal{L}_{\mathrm{val}}$-theory of $(K,v)$ is [finitely undecidable](finitely-undecidable-theories.md). Moreover, if $\mathcal{O}_v$ is definable in $K$ in the language of rings, then $K$ is finitely undecidable as a field.

**Corollary (Tyrrell).** If $(K,v)$ is an NIP henselian nontrivially valued field, its $\mathcal{L}_{\mathrm{val}}$-theory is finitely undecidable, and $K$ is finitely undecidable as a field if $\mathcal{O}_v$ is $\mathcal{L}_r$-definable. Every infinite dp-finite field is finitely undecidable (Corollary 5.9).

Assuming Shelah's conjecture on NIP fields, every infinite NIP field is finitely undecidable (Corollary 5.9(3)).

## Depends on

- [Finitely undecidable theories](finitely-undecidable-theories.md)
- [Complete theory of a first-order structure](../../../first-order-logic/theory-of-structure.md)
- [Field](../../../../Algebra/rings-and-fields/field.md)
- [Separable extension](../../../../FieldTheory/extensions-and-closure/separable-extension.md)

## Proof depends on

- [Separably closed fields are finitely undecidable](separably-closed-fields-are-finitely.md)

## Expansion

By the Ax–Kochen–Ershov principle, an equicharacteristic $0$ henselian field is elementarily equivalent to a Hahn field $k((\Gamma))$ with $k$ and $\Gamma$ countable; Ziegler's method is adapted to find, for each finite subtheory, models in which an undecidable structure is uniformly interpretable. The mixed characteristic case reduces to equicharacteristic $0$ through the coarsening of the valuation, and the Kaplansky case uses separably closed fields of the same imperfection degree. The corollary combines these with classification results on NIP henselian fields and dp-finite fields.

## Sources

- B. Tyrrell, "Finite undecidability in NIP fields", *The Journal of Symbolic Logic* 90(2):509–532, 2025, doi:10.1017/jsl.2023.73; read as arXiv:2210.12729v4, <https://arxiv.org/abs/2210.12729v4>: Corollary 4.10, Theorems 5.3 and 5.8, Corollary 5.9, Definitions 5.4 and 5.5 and Sections 4 and 5 of arXiv:2210.12729v4.
