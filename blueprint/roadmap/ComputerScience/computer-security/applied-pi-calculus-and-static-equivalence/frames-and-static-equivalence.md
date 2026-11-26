# Frames and static equivalence

Fix a signature with an [equational theory](equational-theories-and-convergent-subterm-theories.md) $E$. A *frame* $\varphi = \nu\tilde n.\sigma$ is a substitution
$\sigma = \{M_1/x_1, \dots, M_n/x_n\}$ of terms for variables together with a set $\tilde n$ of restricted names; the terms $M_i$ represent messages seen by the attacker, and
the names in $\tilde n$ are initially unknown to it. Its domain is $\mathrm{dom}(\varphi) = \{x_1, \dots, x_n\}$. A term $t$ is *deducible* from $\varphi$ if $t =_E R\sigma$ for some
term $R$ (a recipe) whose free names avoid $\tilde n$ and whose variables lie in $\mathrm{dom}(\varphi)$.

Two terms $M, N$ are *equal in* $\varphi$, written $(M = N)\varphi$, if their variables lie in $\mathrm{dom}(\varphi)$ and $M\sigma =_E N\sigma$ for some presentation
$\varphi = \nu\tilde n.\sigma$, up to renaming of restricted names, with $\tilde n$ disjoint from the names of $M$ and $N$. Two closed frames $\varphi$ and $\psi$ are
*statically equivalent*, $\varphi \approx_s \psi$, if $\mathrm{dom}(\varphi) = \mathrm{dom}(\psi)$ and for all terms $M, N$, $(M = N)\varphi$ holds if and only if $(M = N)\psi$ does: no
test of equality distinguishes the two sequences of messages. For example, with deterministic encryption the frames
$\nu k.\{\mathrm{aenc}(0, \mathrm{pk}(k))/x, \mathrm{pk}(k)/y\}$ and $\nu k.\{\mathrm{aenc}(1, \mathrm{pk}(k))/x, \mathrm{pk}(k)/y\}$ are not statically equivalent, as the test
$\mathrm{aenc}(0, y) = x$ separates them.

## Depends on

- [Equational theories and convergent subterm theories](equational-theories-and-convergent-subterm-theories.md)

## Sources

- V. Cortier and S. Kremer, "Formal models and techniques for analyzing security protocols: a tutorial", *Foundations and Trends in Programming Languages* 1(3), 2014, doi:10.1561/2500000001, copy at <https://inria.hal.science/hal-01090874>: Section 4.2 (Definitions 4.1–4.5 and Examples 4.4–4.5).
- M. Abadi, B. Blanchet and C. Fournet, "The applied pi calculus: mobile values, new names, and secure communication", *Journal of the ACM* 65(1), 2018, arXiv:1609.03003v2, <https://arxiv.org/abs/1609.03003v2>: Section 4.2, Definitions 4.2–4.3.
