# Löb's axiom is valid on transitive conversely well-founded frames

Let $M$ be a Kripke model whose accessibility relation $R$ is transitive and conversely
well-founded: there is no infinite chain $w_0 \mathrel{R} w_1 \mathrel{R} w_2 \mathrel{R} \cdots$.
Then $\Box(\Box\varphi \to \varphi) \to \Box\varphi$ holds at every world of $M$, for every
formula $\varphi$. A conversely well-founded relation is irreflexive.

Proof: suppose $\Box(\Box\varphi \to \varphi)$ at $w$. By induction along the converse of $R$,
every successor $v$ of $w$ satisfies $\varphi$: its own successors are successors of $w$
(transitivity) and satisfy $\varphi$ by the induction hypothesis, so $\Box\varphi$ and hence
$\varphi$ hold at $v$.

## Background

- [The reverse translation preserves satisfaction](../soundness-and-completeness-of-normal-modal-logic/satisfies-to-proposition.md)
- [Löb's axiom](axiom-lob.md)

## Sources

- R. Verbrugge, "Provability logic", *Stanford Encyclopedia of Philosophy*, substantive revision of 4 March 2024, §3.1.
