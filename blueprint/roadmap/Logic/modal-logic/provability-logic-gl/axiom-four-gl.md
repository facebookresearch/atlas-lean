# GL proves axiom 4

For every formula $\varphi$, $\mathrm{GL} \vdash \Box\varphi \to \Box\Box\varphi$.

Proof: let $\chi = \varphi \wedge \Box\varphi$. The formula

$$\bigl(\Box(\Box\chi \to \chi) \to \Box\chi\bigr) \to (\Box\varphi \to \Box\Box\varphi)$$

is a theorem of K: from $\Box\varphi$ one gets $\Box(\Box\chi \to \chi)$, since at every
successor $\varphi$ holds and $\Box\chi$ gives $\Box\varphi$; and $\Box\chi$ gives
$\Box\Box\varphi$. Its antecedent is an instance of Löb's axiom, so modus ponens gives the
claim. The K theorem is obtained from the completeness of K; the single GL-specific step is the
Löb instance for $\chi$.

## Informally uses

- [Löb's axiom](axiom-lob.md): the instance for $\varphi \wedge \Box\varphi$.
- [Soundness and completeness of K](../soundness-and-completeness-of-normal-modal-logic/derivable-k-iff.md): the K step, checked on all Kripke
  models.
- [Modus ponens with a K theorem](mp-of-k.md)

## Sources

- R. Verbrugge, "Provability logic", *Stanford Encyclopedia of Philosophy*, substantive revision of 4 March 2024, §2.1 (substitution of $A \wedge \Box A$ in the axiom).
