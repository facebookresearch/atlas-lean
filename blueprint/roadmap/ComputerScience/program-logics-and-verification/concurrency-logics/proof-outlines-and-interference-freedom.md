# Proof outlines and interference freedom

An *annotated command* over a state set $\Sigma$ is built from annotated basic actions $\{r\}\,\mathbf{basic}\ f$, sequencing,
annotated conditionals $\{r\}\,\mathbf{if}\ b\ \mathbf{then}\ c_1\ \mathbf{else}\ c_2$, annotated loops $\{r\}\,\mathbf{while}\ b\ \{\mathit{inv}\}\ \mathbf{do}\ c$ and
annotated atomic regions $\{r\}\,\mathbf{await}\ b\ \mathbf{then}\ C$, with assertions $r, \mathit{inv}, b \subseteq \Sigma$. Its *assertions* are all the
annotations it contains, and its *atomic actions* are the pairs $(r, \mathbf{basic}\ f)$ for its annotated basic actions and
$(r \cap b, C)$ for its annotated atomic regions.

- A *proof outline* for a component is a pair $(c, q)$ of an annotated command and a postcondition. It is *locally
  correct* when, read sequentially, each annotation of an atomic action is a valid partial-correctness precondition of
  that action with respect to the next annotation, as derived by the annotated-command rules of the Owicki–Gries system.
- A proof outline $(c', q')$ does not interfere with an assertion $p$ if for every atomic action $(r, a)$ of $c'$ the
  partial-correctness triple $\{p \cap r\}\, a\, \{p\}$ is valid.
- Proof outlines $(c_1, q_1), \dots, (c_n, q_n)$, where a terminated component has no command, are *interference free* if
  for all $i \ne j$ such that component $j$ has a command, $(c_j, q_j)$ does not interfere with $q_i$ nor, when component $i$ has a
  command, with any assertion of $c_i$.

## Sources

- L. Prensa Nieto, *Hoare Logic for Parallel Programs*, Isabelle/HOL theory library (HOL-Hoare_Parallel), document of May 23, 2024, Sections 1.1 and 1.4 (annotated commands, assertions, atomics, interfree-aux, interfree, ann-hoare).
- S. Owicki and D. Gries, "An axiomatic proof technique for parallel programs I", *Acta Informatica* 6(4):319–340, 1976.
- K. R. Apt, F. S. de Boer and E.-R. Olderog, *Verification of Sequential and Concurrent Programs*, 3rd ed., Springer, 2009.
