# Labelled transitions in the applied pi calculus

A label $\alpha$ of the [applied pi calculus](terms-and-processes-of-the-applied-pi-calculus.md) is either an input $N(M)$ or an output $\nu x.\overline{N}\langle x\rangle$ with $x$ not occurring in $N$; the bound
variables are $\mathrm{bv}(N(M)) = \emptyset$ and $\mathrm{bv}(\nu x.\overline{N}\langle x\rangle) = \{x\}$. The *labelled transition* relation $A \xrightarrow{\alpha} A'$ is the smallest relation
satisfying

- (In) $N(x).P \xrightarrow{N(M)} P\{M/x\}$;
- (Out-Var) $\overline{N}\langle M\rangle.P \xrightarrow{\nu x.\overline{N}\langle x\rangle} P \mid \{M/x\}$ for $x \notin \mathrm{fv}(\overline{N}\langle M\rangle.P)$;
- (Scope) if $A \xrightarrow{\alpha} A'$ and $u$ does not occur in $\alpha$, then $\nu u.A \xrightarrow{\alpha} \nu u.A'$;
- (Par) if $A \xrightarrow{\alpha} A'$ and $\mathrm{bv}(\alpha) \cap \mathrm{fv}(B) = \emptyset$, then $A \mid B \xrightarrow{\alpha} A' \mid B$;
- (Struct) if $A \equiv B$, $B \xrightarrow{\alpha} B'$ and $B' \equiv A'$, then $A \xrightarrow{\alpha} A'$,

where $\equiv$ is [structural equivalence](structural-equivalence-in-the-applied-pi-calculus.md). Outputs are by reference: the output term is bound to a fresh
variable exported to the environment.

## Depends on

- [Structural equivalence in the applied pi calculus](structural-equivalence-in-the-applied-pi-calculus.md)
- [Terms and processes of the applied pi calculus](terms-and-processes-of-the-applied-pi-calculus.md)

## Sources

- M. Abadi, B. Blanchet and C. Fournet, "The applied pi calculus: mobile values, new names, and secure communication", *Journal of the ACM* 65(1), 2018, arXiv:1609.03003v2, <https://arxiv.org/abs/1609.03003v2>: Section 4.3, the labels and the rules In, Out-Var, Scope, Par and Struct.
