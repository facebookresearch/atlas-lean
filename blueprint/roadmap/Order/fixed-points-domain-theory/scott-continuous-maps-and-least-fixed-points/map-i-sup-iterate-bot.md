# Kleene's fixed-point theorem for pointed dcpos

Let $D$ be a pointed directed-complete partial order and $f : D \to D$ a Scott-continuous map. Then $\bigsqcup_{n} f^n(\bot)$ is a fixed point of $f$ (S. Abramsky and A. Jung, *Domain Theory*, Handbook of Logic in Computer Science vol. 3 (1994), Theorem 2.1.19 (1); for continuous lattices, D. Scott, *Continuous Lattices*, Oxford PRG-7 (1971), Proposition 3.14).

Here Scott continuity is for directed sets. The statement follows from the ω-chain version, since a Scott-continuous map preserves suprema of ω-chains.

## Background

- [Kleene's fixed point is the least prefixed point](i-sup-iterate-bot-le.md): the other half of Kleene's theorem.
- [The least fixed point is a fixed point](lfp-eq.md): the same statement for ω-continuous maps on ω-complete partial orders.
- [Kleene's supremum for dcpos is the least fixed point of the ω-chain construction](i-sup-iterate-bot-eq-lfp.md): the equation from which this theorem is derived.

## Sources

- D. Scott, *Continuous Lattices*, Technical Monograph PRG-7, Oxford University Computing Laboratory, August 1971, <http://www.cs.ox.ac.uk/files/3229/PRG07.pdf>. This is the pre-publication monograph version of the paper in *Toposes, Algebraic Geometry and Logic*, Lecture Notes in Mathematics 274 (1972), 97–136; theorem numbers here are those of PRG-7.
- S. Abramsky and A. Jung, *Domain Theory*, in *Handbook of Logic in Computer Science*, vol. 3, Clarendon Press, Oxford, 1994. Read in the authors' corrected and expanded online version, which keeps the Handbook's numbering: <https://www.cs.ox.ac.uk/people/samson.abramsky/handbook.pdf>.
