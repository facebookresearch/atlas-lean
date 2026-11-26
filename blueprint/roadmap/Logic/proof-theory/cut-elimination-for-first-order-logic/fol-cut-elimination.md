# Gentzen's cut elimination for first-order logic

Gentzen's Hauptsatz: in a standard classical sequent calculus for first-order logic, every sequent derivable with the cut rule is derivable without it. Standard calculi here are Gentzen's LK, with the structural rules of weakening, exchange and contraction, and calculi such as G3c, whose contexts are multisets and whose left rules may act on any formula of the context.

The structural rules matter. In the [calculus with cut](sequent.md) and its [cut-free fragment](cut-free-sequent.md), whose left rules act only on the first formula of the context and which have no exchange or contraction rule, cut cannot be eliminated. For an atomic formula $p$, the sequent $p, \neg p \Rightarrow \bot$ is derivable with cut (cut on $\neg p$, then $\to$ left with two assumptions) but not without: every cut-free rule that could conclude $\neg\bot, \dots, \neg\bot, p, \neg p \Rightarrow \bot$ has a premise of the same form.

## Sources

- G. Gentzen, "Untersuchungen über das logische Schließen I", *Mathematische Zeitschrift* 39 (1935), 176-210.
- H. Enderton, *A Mathematical Introduction to Logic*, 2nd ed., Academic Press, 2001, §2.5.
- S. Buss, "An Introduction to Proof Theory", in *Handbook of Proof Theory*, Elsevier, 1998, §2.
