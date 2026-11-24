# The Gödel sentence of GL

The consistency statement $\neg\Box\bot$ is a fixed point of $\neg\Box p$ in GL:

$$\mathrm{GL} \vdash \neg\Box\bot \to \neg\Box\neg\Box\bot \quad\text{and}\quad
\mathrm{GL} \vdash \neg\Box\neg\Box\bot \to \neg\Box\bot .$$

Arithmetically, by the uniqueness of fixed points, the sentences asserting their own
unprovability are exactly those PA-provably equivalent to $\mathrm{Con}(\mathrm{PA})$.

Proof: the first implication is the modal second incompleteness theorem. The second is a theorem
of K: $\Box\bot$ implies $\Box\psi$ for every $\psi$.

## Informally uses

- [Modal Gödel's second incompleteness theorem](godel-second-gl.md)
- [Modus ponens with a K theorem](mp-of-k.md)

## Background

- [The de Jongh–Sambin fixed point for one boxed occurrence](fixed-point-gl-of-box.md): gives the
  fixed point $\neg\Box\neg\top$ of $\neg\Box p$, equivalent to this one.
- [Uniqueness of fixed points in GL](fixed-point-unique-gl.md)

## Sources

- R. Verbrugge, "Provability logic", *Stanford Encyclopedia of Philosophy*, substantive revision of 4 March 2024, §2.2.
