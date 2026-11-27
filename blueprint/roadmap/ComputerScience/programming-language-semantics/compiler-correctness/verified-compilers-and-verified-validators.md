# Verified compilers and verified validators

Fix a notion $S \approx C$ of [semantic preservation](notions-of-semantic-preservation.md) between source programs $S$ and compiled programs $C$. A *compiler* is a total function $\mathrm{Comp}$ from source programs to either compiled code, $\mathrm{Comp}(S) = \mathrm{OK}(C)$, or a compile-time error, $\mathrm{Comp}(S) = \mathrm{Error}$. It is *verified* if it is accompanied by a formal proof of

$$\forall S, C.\ \mathrm{Comp}(S) = \mathrm{OK}(C) \implies S \approx C.$$

A *validator* is a Boolean-valued function $\mathrm{Validate}(S, C)$; it is *verified* if it is accompanied by a formal proof that $\mathrm{Validate}(S, C) = \mathrm{true}$ implies $S \approx C$. A compiler or validator that satisfies the implication but comes with no proof is correct, not verified. A compiler that always fails is verified, with a vacuous proof: verification constrains only the code that is produced.

The *monadic composition* of compilers $\mathrm{Comp}_1$ from $L_1$ to $L_2$ and $\mathrm{Comp}_2$ from $L_2$ to $L_3$ returns $\mathrm{Error}$ if $\mathrm{Comp}_1(S) = \mathrm{Error}$ and $\mathrm{Comp}_2(I)$ if $\mathrm{Comp}_1(S) = \mathrm{OK}(I)$.

## Depends on

- [Notions of semantic preservation](notions-of-semantic-preservation.md)

## Sources

- X. Leroy, "A formally verified compiler back-end", *Journal of Automated Reasoning* 43(4):363–446, 2009, <https://xavierleroy.org/publi/compcert-backend.pdf>, Section 2.2, Definition 8 (verified compiler) and Definition 9 (verified validator), and Section 2.3, the monadic composition of compilers.
