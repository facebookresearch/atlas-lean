# Goldwasser–Micali's main theorem for one bit, per adversary

For every key distribution and every eavesdropper $A$, the eavesdropping ($\mathsf{PubK}^{\mathrm{eav}}$)
advantage of $A$ against the [one-bit Goldwasser–Micali scheme](scheme.md) equals half the advantage,
in the [residuosity experiment](qr-exp.md), of the [reduction](reduction.md) built from $A$ with one
call and the same coins. So an eavesdropper with guessing advantage $\varepsilon$ gives a
distinguisher of $x^2$ from $y x^2$ with advantage $2\varepsilon$, and an efficient eavesdropper an
efficient distinguisher. No assumption on the keys is needed for this identity.

The factor $\tfrac12$ is the usual one between the guessing advantage
$\lvert \Pr[\text{win}] - \tfrac12 \rvert$ and a distinguishing advantage. The residuosity experiment
gives the distinguisher the key element $y$ and samples $x^2$ against $y x^2$; its identification with
the standard problem (uniform residues against uniform non-residues of Jacobi symbol $+1$) is a
separate step, so this reduction is close to definitional.

## Informally uses

- [The reduction for one key and one coin](inner-identity.md)
- [Averaging a pointwise identity between sums of success probabilities](../../security-games/games-and-advantages/apply-true-bind-add-eq.md)

## Sources

- S. Goldwasser and S. Micali, "Probabilistic encryption & how to play mental poker keeping secret all partial information", Proc. 14th ACM STOC (1982), 365-377, Section 4 (the security of the cryptosystem, for one bit).
- J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014, Definition 11.2 (the experiment $\mathsf{PubK}^{\mathrm{eav}}$).
