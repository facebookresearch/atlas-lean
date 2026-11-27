# Term models of the computational metalanguage

Every theory $\mathcal{T}$ of [the computational metalanguage](the-computational-metalanguage-and-its-interpretation.md), viewed as a category $F(\mathcal{T})$ whose objects are types and
whose morphisms $\tau_1 \to \tau_2$ are terms $x : \tau_1 \vdash e : \tau_2$ up to provable equality, has finite products and a [strong monad](strong-monads.md) whose tensorial strength is

$$t_{\tau_1, \tau_2} = [\, x : \tau_1 \times T\tau_2 \vdash (\mathrm{let}_T\ x_2 \Leftarrow \pi_2\, x\ \mathrm{in}\ [\langle \pi_1\, x, x_2 \rangle]_T) : T(\tau_1 \times \tau_2) \,]_{\mathcal{T}}.$$

Its monad is given as for the simple metalanguage: $T(\tau) = T\tau$, $\eta_\tau = [x : \tau \vdash [x]_T : T\tau]_{\mathcal{T}}$, and
$([x : \tau_1 \vdash e : T\tau_2]_{\mathcal{T}})^* = [x' : T\tau_1 \vdash (\mathrm{let}_T\ x \Leftarrow x'\ \mathrm{in}\ e) : T\tau_2]_{\mathcal{T}}$, with composition given by substitution and identities by
variables.

## Depends on

- [The computational metalanguage and its interpretation](the-computational-metalanguage-and-its-interpretation.md)

## Sources

- E. Moggi, "Notions of computation and monads", *Information and Computation* 93(1):55–92, 1991, <https://doi.org/10.1016/0890-5401(91)90052-4>: Section 3.1, Proposition 3.8, with Definition 2.4 and Proposition 2.5 for the corresponding construction for the simple metalanguage.
