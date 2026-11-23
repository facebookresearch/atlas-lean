# Modal Gödel's second incompleteness theorem

$$\mathrm{GL} \vdash \neg\Box\bot \to \neg\Box\neg\Box\bot .$$

Read arithmetically: if PA is consistent, PA does not prove its own consistency statement
$\neg\mathrm{Prov}(\ulcorner\bot\urcorner)$.

Proof: $\neg\Box\bot$ is $\Box\bot \to \bot$, so the instance
$\Box(\Box\bot \to \bot) \to \Box\bot$ of Löb's axiom reads $\Box\neg\Box\bot \to \Box\bot$;
its contrapositive is the claim (a propositional step, taken from K).

## Informally uses

- [Löb's axiom](axiom-lob.md): the instance for $\bot$.
- [Modus ponens with a K theorem](mp-of-k.md)

## Background

- [Gödel's second incompleteness theorem, abstract Hilbert–Bernays–Löb form](../../proof-theory/g-del-s-incompleteness-theorems/hilbert-bernays-lob-second-incompletenes.md): the
  arithmetical theorem whose modal form this is.

## Sources

- R. Verbrugge, "Provability logic", *Stanford Encyclopedia of Philosophy*, substantive revision of 4 March 2024, §2.2 and §4.1.
