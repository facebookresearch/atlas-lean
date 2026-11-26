# Kripke completeness of intuitionistic propositional logic

If every [Kripke model](kripke-models-for-ipc.md) $\mathcal{C}$ with $\mathcal{C} \Vdash \Gamma$ satisfies $\mathcal{C} \Vdash \varphi$, then $\Gamma \vdash \varphi$ in [natural deduction for IPC](natural-deduction-for-intuitionistic-propositional-logic.md). With soundness, $\Gamma \vdash \varphi$ holds exactly when $\varphi$ is forced in every Kripke model forcing $\Gamma$.

**Proof.** If $\Gamma \nvdash \varphi$, then by [completeness for Heyting algebras](soundness-and-completeness-of-ipc-for-heyting-algebras.md) some $H, v$ satisfies $\Gamma$ but not $\varphi$, so $v(\varphi) \ne 1$ and hence $0 \ne 1$ in $H$, and the [Kripke model of prime filters](heyting-algebras-embed-into-kripke-models.md) of $H$ forces $\Gamma$ but not $\varphi$.

## Depends on

- [Natural deduction for intuitionistic propositional logic](natural-deduction-for-intuitionistic-propositional-logic.md)
- [Kripke models for intuitionistic propositional logic](kripke-models-for-ipc.md)

## Proof depends on

- [Kripke soundness of intuitionistic propositional logic](kripke-soundness-of-ipc.md)
- [Soundness and completeness of IPC for Heyting algebras](soundness-and-completeness-of-ipc-for-heyting-algebras.md)
- [Heyting algebra valuations are represented by Kripke models](heyting-algebras-embed-into-kripke-models.md)

## Sources

- M. H. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, 1998 (published as volume 149 of *Studies in Logic and the Foundations of Mathematics*, Elsevier, 2006), Section 2.5: Theorem 2.5.6, the right-to-left part, and its proof.
