# Conservative extensions and Σ-entailment in fragments of first-order logic

For a fragment $F$ of first-order logic, $\varphi_1$ $\Sigma$-entails $\varphi_2$ when every $F$-sentence over the signature $\Sigma$ that follows from $\varphi_2$ follows from $\varphi_1$; $\varphi_1 \wedge \varphi_2$ is a conservative extension of $\varphi_1$ when it entails no new $F$-sentence in the signature of $\varphi_1$.

Let $F$ be a fragment of first-order logic, $\varphi_1, \varphi_2$ $F$-sentences and $\Sigma$ a signature; $F(\Sigma)$ is the set of $F$-sentences using only symbols of $\Sigma$.

1. $\varphi_1$ *$\Sigma$-entails* $\varphi_2$, written $\varphi_1 \models_\Sigma \varphi_2$, if for all $F(\Sigma)$-sentences $\psi$, $\varphi_2 \models \psi$ implies $\varphi_1 \models \psi$.
2. $\varphi_1$ and $\varphi_2$ are *$\Sigma$-inseparable* if each $\Sigma$-entails the other.
3. $\varphi_1 \wedge \varphi_2$ is a *conservative extension* of $\varphi_1$ if $\varphi_1$ $\mathrm{sig}(\varphi_1)$-entails $\varphi_1 \wedge \varphi_2$, where $\mathrm{sig}(\varphi_1)$ is the set of symbols of $\varphi_1$.
4. $\varphi_1$ *strongly $\Sigma$-entails* $\varphi_2$ if $\varphi_1$ $\Sigma'$-entails $\varphi_2$ for every signature $\Sigma'$ with $\Sigma' \cap \mathrm{sig}(\varphi_2) \subseteq \Sigma$.

The notions depend on $F$, because the witness sentences $\psi$ range over $F(\Sigma)$. The decision problems take $\varphi_1$, $\varphi_2$ and, where it occurs, $\Sigma$ as input. As in the source, sentences may use equality, which is a logical symbol and not part of any signature, and contain no function symbols or constants; signatures are finite sets of predicates, and in $\mathrm{FO}^2$ and its fragments only predicates of arity one and two are used, which the source notes loses no generality.

## Depends on

- [Guarded fragment of first-order logic](../guarded-and-fluted-fragments/guarded-fragment.md)
- [Two-variable logic and its counting extension](../two-variable-logic-and-its-extensions/two-variable-logic-and-its-counting-extension.md)

## Proof depends on

None.

## Sources

- Jean Christoph Jung, Carsten Lutz, Mauricio Martel, Thomas Schneider and Frank Wolter, "Conservative extensions in guarded and two-variable fragments", in *44th International Colloquium on Automata, Languages, and Programming (ICALP 2017)*, LIPIcs 80, 108:1–108:14, 2017, doi:[10.4230/LIPIcs.ICALP.2017.108](https://doi.org/10.4230/LIPIcs.ICALP.2017.108). Numbering of the version read, arXiv:1705.10115v1: Definition 1 and the definition of strong $\Sigma$-entailment in Section 2.
