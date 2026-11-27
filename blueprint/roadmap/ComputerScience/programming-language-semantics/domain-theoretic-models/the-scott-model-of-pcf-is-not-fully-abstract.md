# The Scott model of PCF is not fully abstract

Consider Plotkin's PCF, with ground types $o$ (truth values) and $\iota$ (natural numbers), call-by-name evaluation, and its standard Scott model, in which each type denotes a domain of continuous functions. The model is adequate: denotational equality of terms implies operational (contextual) equivalence. The converse fails.

For $i = 0, 1$, let $M_i$ be the closed term of type $(o \to o \to o) \to \iota$ given by

$$M_i = \lambda a.\ \mathrm{if}\ a\,\mathit{tt}\,\Omega\ \mathrm{then}\ \bigl(\mathrm{if}\ a\,\Omega\,\mathit{tt}\ \mathrm{then}\ (\mathrm{if}\ a\,\mathit{ff}\,\mathit{ff}\ \mathrm{then}\ \Omega\ \mathrm{else}\ i)\ \mathrm{else}\ \Omega\bigr)\ \mathrm{else}\ \Omega,$$

where $\Omega$ is a divergent term of the appropriate ground type.

- **Different denotations.** Applied to parallel or, the continuous function $V$ with $V(\mathit{tt}, x) = V(x, \mathit{tt}) = \mathit{tt}$ for all $x$ and $V(\mathit{ff}, \mathit{ff}) = \mathit{ff}$, the denotation of $M_i$ yields $i$. So $M_0$ and $M_1$ have different denotations.
- **Operational equivalence.** $M_0$ and $M_1$ are operationally equivalent: no program context distinguishes them. The proof uses the activity lemma, a sequentiality property of PCF evaluation. If $C[M_0]$ terminated and $C[M_1]$ did not terminate with the same value, the argument supplied to $a$ would have to evaluate to $\mathit{tt}$ both with $\Omega$ as first argument and with $\Omega$ as second argument, and to $\mathit{ff}$ on $(\mathit{ff}, \mathit{ff})$. No PCF term behaves this way.

Hence the Scott model is not fully abstract for PCF. When PCF is extended with a parallel conditional, the same model becomes fully abstract.

## Background

- [Computational adequacy for PCF](../pcf-and-computational-adequacy/adequacy.md): the single-ground-type version of adequacy
- [Contextual equivalence in PCF](../pcf-and-computational-adequacy/ctx-equiv.md)

## Sources

- G. D. Plotkin, "LCF considered as a programming language", *Theoretical Computer Science* 5(3):223–255, 1977, <https://homepages.inf.ed.ac.uk/gdp/publications/LCF.pdf>, Section 4: Theorem 4.1, the terms $M_0, M_1$ of Fig. 5, the functions of Tables 1 and 2, and the activity lemma (Lemma 4.2) with the argument that follows it; Theorem 4.3 (full abstraction with the parallel conditional).
