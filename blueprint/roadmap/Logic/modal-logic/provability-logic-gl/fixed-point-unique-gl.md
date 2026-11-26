# Uniqueness of fixed points in GL

Let $p$ be modalised in $A$, and write $A(\theta)$ for $A[p := \theta]$. For all formulas $\psi$ and
$\chi$,

$$\mathrm{GL} \vdash \boxdot(\psi \leftrightarrow A(\psi)) \to \boxdot(\chi \leftrightarrow A(\chi)) \to
(\psi \leftrightarrow \chi),$$

where $\boxdot\theta$ abbreviates $\theta \wedge \Box\theta$; written out, the statement has four hypotheses, as curried implications. In particular two fixed points of $A$ are GL-provably
equivalent: if $\mathrm{GL} \vdash \psi \leftrightarrow A(\psi)$ and
$\mathrm{GL} \vdash \chi \leftrightarrow A(\chi)$, necessitation gives the four hypotheses, so
$\mathrm{GL} \vdash \psi \leftrightarrow \chi$. This rule is the form in which the source below
states uniqueness; the internal form above is stronger and is derived here.

Proof: let $r = \psi \leftrightarrow \chi$. On a transitive model, assume the hypotheses at $w$. At a
successor $v$ of $w$ where $\Box r$ holds, $A(\psi)$ and $A(\chi)$ agree, because $p$ is read only
at successors of $v$; so $r$ holds at $v$. This gives $\Box(\Box r \to r)$ at $w$, the Löb
instance for $r$ gives $\Box r$, and the same argument at $w$ gives $r$. The whole implication,
with the Löb instance as an extra hypothesis, is therefore valid on transitive models, hence a K4
theorem; modus ponens with the Löb instance gives the GL theorem.

## Informally uses

- [Löb's axiom](axiom-lob.md): the instance for $\psi \leftrightarrow \chi$.
- [A modalised atom is read only at visible worlds](satisfies-update-atom-congr-of-modalised.md)
- [Semantic substitution lemma](../kripke-semantics/satisfies-subst.md)
- [K4-theorems are the formulas valid in every transitive Kripke model](../soundness-and-completeness-of-normal-modal-logic/derivable-k4-iff.md)
- [Modus ponens with a K4 theorem in GL](mp-of-k4.md)

## Sources

- R. Verbrugge, "Provability logic", *Stanford Encyclopedia of Philosophy*, substantive revision of 4 March 2024, §2.2
  (uniqueness of fixed points, stated as a rule).
