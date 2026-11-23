# The de Jongh–Sambin fixed point for one boxed occurrence

Let $B$ and $C$ be formulas and $p$, $r$ atoms, with $p$ not occurring in $B$, and let
$A = B[r := \Box C]$, so that $A(p) = B(\Box C(p))$ and every occurrence of $p$ in $A$ is inside
the boxed subformula $\Box C$. Put

$$H = B\bigl[r := \Box\, C[p := B[r := \top]]\bigr], \qquad\text{i.e. } H = B(\Box C(B(\top))).$$

Then $\mathrm{GL} \vdash H \leftrightarrow A(H)$. Examples: for $\neg\Box p$ ($B = \neg r$,
$C = p$) the fixed point is $\neg\Box\neg\top$, equivalent to $\neg\Box\bot$; for
$\Box(p \to q)$ ($B = r$) it is $\Box(\top \to q)$, equivalent to $\Box q$.

Proof: let $X = C(B(\top))$. On a transitive model, wherever $\Box X$ holds it holds at all
successors, so $H$ and $B(\top)$ agree on the generated cone and hence $C(H)$ and $X$ agree there;
thus $\Box X \to \Box C(H)$. Conversely, if $\Box C(H)$ holds at a world where Löb's axiom for $X$
holds, every successor satisfying $\Box X$ satisfies $X$, so Löb's axiom gives $\Box X$. So
$\Box C(H) \leftrightarrow \Box X$ on the cone of any world where Löb's axiom for $X$ and its
necessitation hold, and there $H \leftrightarrow A(H)$ by locality. This implication is a K4
theorem, and the Löb instance for $X$ and its necessitation are GL theorems.

The source below states the de Jongh–Sambin theorem for every formula in which $p$ is modalised,
and the example $\neg\Box p$ with fixed point $\neg\Box\bot$; it does not give the explicit
formula $B(\Box C(B(\top)))$, which is derived here together with its proof. The general theorem is the de Jongh–Sambin fixed point theorem.

## Informally uses

- [Löb's axiom](axiom-lob.md): the instance for $C(B(\top))$, and its necessitation.
- [Semantic substitution lemma](../kripke-semantics/satisfies-subst.md)
- [Truth depends only on the visible part of the valuation](../kripke-semantics/satisfies-congr.md)
- [K4-theorems are the formulas valid in every transitive Kripke model](../soundness-and-completeness-of-normal-modal-logic/derivable-k4-iff.md)
- [Modus ponens with a K4 theorem in GL](mp-of-k4.md)

## Sources

- R. Verbrugge, "Provability logic", *Stanford Encyclopedia of Philosophy*, substantive revision of 4 March 2024, §2.2
  (the fixed point theorem and the example $\neg\Box p$).
