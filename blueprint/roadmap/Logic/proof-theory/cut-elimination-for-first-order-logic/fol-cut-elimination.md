# Cut elimination fails for the restricted first-order sequent calculus

The held declaration states cut elimination for the [calculus with cut](sequent.md) of this topic: every sequent derivable in it is derivable in its [cut-free fragment](cut-free-sequent.md). These calculi are not Gentzen's LK. Their left rules act only on the first formula of the context, and they have no exchange or contraction rule.

For them the statement is false, and the declaration is held back (#10491). For an atomic formula $p$, the sequent $p, \neg p \Rightarrow \bot$ is derivable with cut (cut on $\neg p$, then $\to$ left with two assumptions) but not without: every cut-free rule that could conclude $\neg\bot, \dots, \neg\bot, p, \neg p \Rightarrow \bot$ has a premise of the same form.

Cut elimination holds once the left rules may act on any formula of the context, or once exchange and contraction are added. Gentzen's Hauptsatz for LK, with its structural rules, is [cut elimination for the classical sequent calculus](../cut-elimination-for-the-classical-sequent-calculus.md).

## Depends on

- [A classical sequent calculus for first-order logic with cut](sequent.md)
- [The cut-free sequent calculus for first-order logic](cut-free-sequent.md)

## Sources

- G. Gentzen, "Untersuchungen über das logische Schließen I", *Mathematische Zeitschrift* 39 (1935), 176-210.
- S. Buss, "An Introduction to Proof Theory", in *Handbook of Proof Theory*, Elsevier, 1998, §2.
