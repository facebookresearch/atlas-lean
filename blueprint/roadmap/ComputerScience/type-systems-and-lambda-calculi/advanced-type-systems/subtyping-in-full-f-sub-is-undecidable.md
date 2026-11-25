# Subtyping in full F-sub is undecidable

With the rowing machines, the encoding $F$ and the closed types $\sigma_w$ of
[encoding two-counter machines in full F-sub subtyping](encoding-two-counter-machines-in-full-f-sub.md):

- a rowing machine $M$ of width $w$ halts if and only if $\sigma_w <: F(M)$ is derivable;
- the halting problem of two-counter machines reduces to that of rowing machines, and it is undecidable;
- hence subtyping in full $F_{<:}$ is undecidable, already in the fragment without arrow types;
- type checking of full $F_{<:}$ is also undecidable: for each subtyping question there is a term that type checks exactly when the subtyping
  judgment holds.

## Depends on

- [Encoding two-counter machines in full F-sub subtyping](encoding-two-counter-machines-in-full-f-sub.md)
- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Proof depends on

- [Encoding two-counter machines in full F-sub subtyping](encoding-two-counter-machines-in-full-f-sub.md)

## Sources

- R. Álvarez Castro, *Mechanized Undecidability of Subtyping in System F*, Master's thesis, Saarland University, <https://ps.uni-saarland.de/~alvarez/thesis.pdf>: Theorems 4.8, 4.13–4.14, 5.5, 5.9, 5.13, 5.17, 5.18 and 5.21 (Section 5.3).
