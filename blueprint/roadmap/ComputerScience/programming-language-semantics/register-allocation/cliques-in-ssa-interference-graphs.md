# Interfering variables of a strict SSA program are simultaneously live

Let $P$ be a strict program in SSA form with its interference graph, in the sense of [interference in strict SSA programs](interference-in-strict-ssa-programs.md).

**Theorem.** For every clique $C$ of the interference graph there is a label at which all variables of $C$ are live. So the size of the largest clique equals the largest number of variables live at one label. The convention that a variable is live at its definition and has a use matters for single variables: in $x \leftarrow 0;\ \mathtt{return}\ 1$, without it the clique $\{x\}$ would have no label where $x$ is live.

**Proof.** By [the comparability lemma](interfering-ssa-variables-have-comparable-defi.md) the defining labels of the variables of $C$ are totally ordered by dominance, so they can be listed as $D_{c_1}, \dots, D_{c_n}$ with each dominating the next. By [the liveness lemma](the-earlier-of-two-interfering-ssa-variables.md) every $c_i$ is live at $D_{c_n}$.

## Depends on

- [Interference in strict SSA programs](interference-in-strict-ssa-programs.md)

## Proof depends on

- [Interfering SSA variables have comparable definitions](interfering-ssa-variables-have-comparable-defi.md)
- [The earlier of two interfering SSA variables is live at the later definition](the-earlier-of-two-interfering-ssa-variables.md)

## Sources

- S. Hack, D. Grund and G. Goos, "Register allocation for programs in SSA-form", *Compiler Construction (CC 2006)*, LNCS 3923, Springer, 2006, pp. 247–262, <https://compilers.cs.uni-saarland.de/papers/ssara.pdf>, Section 2: Definitions 1–3 (dominance, strict programs, interference) and Theorem 1 with its proof.
