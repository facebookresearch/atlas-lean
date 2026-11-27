# Cut elimination for first-order logic

- [A classical sequent calculus for first-order logic with cut](sequent.md)
- [The cut-free sequent calculus for first-order logic](cut-free-sequent.md)
- [Cut elimination for the classical sequent calculus LK](../cut-elimination-for-the-classical-sequent-calculus.md)

Cut elimination fails for the restricted calculus of this topic, in which the left rules act only on the first formula of the context: $p, \neg p \Rightarrow \bot$ is derivable with cut but not without ([issue 10491](https://github.com/facebookresearch/atlas-lean/issues/10491)). Gentzen's Hauptsatz for LK is [cut elimination for the classical sequent calculus](../cut-elimination-for-the-classical-sequent-calculus.md).
