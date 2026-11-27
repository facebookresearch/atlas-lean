# Finite elements are definable in PCF with the parallel conditional

In the standard model of [PCF with the parallel conditional](pcf-with-the-parallel-conditional.md), every domain $D_\sigma$ is a consistently complete algebraic cpo, and its
finite (compact) elements are the least upper bounds of the finite sets $F$ of step functions $(d_1 \Rightarrow (\cdots (d_n \Rightarrow d) \cdots))$, built from finite elements of
the argument domains and an element $d \ne \bot$ of a ground domain, that have an upper bound (Scott); such a set has one exactly when any two of its steps whose
inputs $d_i, d_i'$ are pairwise compatible have the same output. Every finite element of every $D_\sigma$ is the denotation of a closed term of $\mathcal{L}_{PA}$.

The proof is by induction on types, showing at the same time that for finite $e$ and $f$ in $D_\sigma$ the functions $(e \Rightarrow \mathit{tt})$ and, when it exists,
$(e \Rightarrow \mathit{tt}) \sqcup (f \Rightarrow \mathit{ff})$ are definable.

## Depends on

- [PCF with the parallel conditional](pcf-with-the-parallel-conditional.md)

## Sources

- G. D. Plotkin, "LCF considered as a programming language", *Theoretical Computer Science* 5(3):223–255, 1977, <https://homepages.inf.ed.ac.uk/gdp/publications/LCF.pdf>: Section 4, the definitions of finite elements, algebraic and consistently complete cpos and step functions $(d \Rightarrow e)$ on pages 237–238, Lemma 4.4 (Scott) and Lemma 4.5 (every finite element is definable).
