# Basic properties of stable models

This node collects basic properties of stable models of finite ground normal logic programs, all under
the Gelfond–Lifschitz reduct definition.

## Expansion

A sound expansion has separate pages for:

1. **Minimality.** Every stable model of $P$ is a minimal model of $P$ read as a set of classical
   implications.
2. **Supportedness.** Every atom of a stable model $X$ is the head of a rule of $P$ whose positive body is
   contained in $X$ and whose negative body is disjoint from $X$.
3. **Definite programs.** A program without negation has exactly one stable model, its least model.
4. **Number of stable models.** $p \leftarrow \mathrm{not}\ p$ has no stable model, and
   $p \leftarrow \mathrm{not}\ q$, $q \leftarrow \mathrm{not}\ p$ has the two stable models $\{p\}$ and $\{q\}$.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Gelfond-Lifschitz reduct and stable models.

## Sources

- V. Lifschitz, *Twelve definitions of a stable model*, ICLP 2008, LNCS 5366, 37–51, Section 5 (Definition C, stable models through the reduct) and Section 2.1 (minimal models of definite programs). Items 1–4 follow directly from Definition C: a model of $P$ contained in a stable model $X$ is a model of the reduct $P^X$; a definite program equals its reduct; the examples are checked by enumerating the four interpretations. <https://www.cs.utexas.edu/~vl/papers/12defs.pdf>
