# Internal reduction in the applied pi calculus

*Internal reduction* $\to$ is the smallest relation on [extended processes](terms-and-processes-of-the-applied-pi-calculus.md) that is closed under
[structural equivalence](structural-equivalence-in-the-applied-pi-calculus.md) and application of evaluation contexts and contains

$$\overline{N}\langle x\rangle.P \mid N(x).Q \to P \mid Q \ (\text{Comm}), \qquad \mathbf{if}\ M = M\ \mathbf{then}\ P\ \mathbf{else}\ Q \to P \ (\text{Then}),$$

$$\mathbf{if}\ M = N\ \mathbf{then}\ P\ \mathbf{else}\ Q \to Q \ \text{ for ground terms } M, N \text{ with } \Sigma \not\vdash M = N \ (\text{Else}).$$

Communication of an arbitrary term follows with Alias and Subst: $\overline{N}\langle M\rangle.P \mid N(x).Q \to^* P \mid Q\{M/x\}$ up to $\equiv$, for $x$ not free in $N$, $M$ and
$P$. $\to^*$ is the reflexive and transitive closure of $\to$.

## Depends on

- [Structural equivalence in the applied pi calculus](structural-equivalence-in-the-applied-pi-calculus.md)
- [Terms and processes of the applied pi calculus](terms-and-processes-of-the-applied-pi-calculus.md)

## Sources

- M. Abadi, B. Blanchet and C. Fournet, "The applied pi calculus: mobile values, new names, and secure communication", *Journal of the ACM* 65(1), 2018, arXiv:1609.03003v2, <https://arxiv.org/abs/1609.03003v2>: Section 2.2, the rules Comm, Then and Else and the derivation of term communication.
