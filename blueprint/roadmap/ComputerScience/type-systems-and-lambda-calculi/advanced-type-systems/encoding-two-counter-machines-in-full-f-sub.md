# Encoding two-counter machines in full F-sub subtyping

Consider full $F_{<:}$ without arrows: types $x \mid \top \mid \forall x{<:}\sigma.\, \tau$, with reflexivity, transitivity, $\Gamma \vdash \tau <: \top$, $\Gamma \vdash x <: \Gamma[x]$ and the
quantifier rule that is contravariant in the bound and rebinds the body,

$$\frac{\Gamma \vdash \tau_1 <: \sigma_1 \qquad \Gamma, x{<:}\tau_1 \vdash \sigma_2 <: \tau_2}{\Gamma \vdash \forall x{<:}\sigma_1.\, \sigma_2 <: \forall x{<:}\tau_1.\, \tau_2}.$$

A *rowing machine* of width $w > 0$ is a vector $\langle \rho_1, \dots, \rho_w \rangle$ of closed rows, where a row is a variable $x_i$ ($i \le w$), $\mathrm{Halt}$, or an
abstract row $\lambda x_1, \dots, x_w.\, \langle \rho'_1, \dots, \rho'_w \rangle$. If $\rho_1$ is such an abstract row, the machine steps to
$\langle \rho'_1[\vec\rho/\vec x], \dots, \rho'_w[\vec\rho/\vec x] \rangle$, and it *halts* if it reaches a machine whose first row is $\mathrm{Halt}$.

1. **Two-counter machines to rowing machines.** For a two-counter machine $M$ with program length $w$ there is a computable rowing machine
   $R(M)$ of width $w + 5$, storing the program counter, both counters and the branch targets in its first five registers and the encoded
   instructions in the rest, such that $M$ halts if and only if $R(M)$ halts.
2. **Rowing machines to subtyping.** There is a computable encoding $F$ of rows as types with $w + 1$ polyadic bounded quantifiers, and a fixed
   closed type $\sigma_w$, such that if $M$ steps to $M'$, then $\sigma_w <: F(M)$ has a derivation of height $n + 2$ in a deterministic variant of the
   subtyping system exactly when $\sigma_w <: F(M')$ has one of height $n$; and $\sigma_w <: F(\langle \mathrm{Halt}, \rho_2, \dots, \rho_w \rangle)$ is derivable. In the
   deterministic variant each judgment is the conclusion of at most one rule, so each machine step corresponds to two fixed subtyping steps.

## Depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Sources

- R. Álvarez Castro, *Mechanized Undecidability of Subtyping in System F*, Master's thesis, Saarland University, <https://ps.uni-saarland.de/~alvarez/thesis.pdf>: Definition 5.1, Sections 4.1–4.3 (Definitions 4.1–4.3 and 4.9–4.12, Theorem 4.13), Section 5.1 (the intermediate systems) and Section 5.2 (Definition 5.14 and Lemmas 5.15–5.16).
