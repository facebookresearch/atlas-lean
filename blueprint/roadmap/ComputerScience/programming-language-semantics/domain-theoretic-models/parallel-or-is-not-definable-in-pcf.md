# Parallel or is not definable in PCF

In Plotkin's PCF with its standard Scott model, the parallel-or function $V$, the continuous function on truth values with $V(\mathit{tt}, x) = V(x, \mathit{tt}) = \mathit{tt}$ for all $x$ and $V(\mathit{ff}, \mathit{ff}) = \mathit{ff}$, is not the denotation of any closed PCF term. By monotonicity $V(\bot, \bot) = \bot$, since it lies below both $\mathit{tt}$ and $\mathit{ff}$.

**Proof.** Let $M_0$ and $M_1$ be the terms of the [failure of full abstraction](the-scott-model-of-pcf-is-not-fully-abstract.md). They are operationally equivalent, and their denotations applied to $V$ are $0$ and $1$. If a closed term $P$ denoted $V$, the programs $M_0 P$ and $M_1 P$ would denote $0$ and $1$. By adequacy they would evaluate to different numerals, so the context $[\,]\,P$ would distinguish $M_0$ from $M_1$, a contradiction.

## Proof depends on

- [The Scott model of PCF is not fully abstract](the-scott-model-of-pcf-is-not-fully-abstract.md)

## Sources

- G. D. Plotkin, "LCF considered as a programming language", *Theoretical Computer Science* 5(3):223–255, 1977, <https://homepages.inf.ed.ac.uk/gdp/publications/LCF.pdf>, Section 4: Theorem 4.1 (adequacy implies that denotational equivalence entails operational equivalence), Tables 1 and 2 (the parallel functions $V$ and $V'$), and the discussion following the activity lemma: the domains contain parallel functions that the deterministic operational semantics cannot realize.
