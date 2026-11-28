# Fancy update modality

The *fancy update modality* ${}^{\mathcal{E}_1}|\!\Rrightarrow^{\mathcal{E}_2} P$ is defined from world satisfaction, enabled-invariant tokens, the basic update and except-0. It combines frame-preserving updates, removal of laters from timeless propositions, and opening or closing of invariants; Iris view shifts are defined from it.

With masks $\mathcal{E}, \mathcal{E}_1, \mathcal{E}_2 \subseteq \mathbb{N}$ and the enabled-token ownership $[\mathcal{E}]^{\gamma_{\mathrm{EN}}}$,

$$
{}^{\mathcal{E}_1}|\!\Rrightarrow^{\mathcal{E}_2} P \triangleq W \ast [\mathcal{E}_1]^{\gamma_{\mathrm{EN}}} \mathrel{-\!\!\ast} \dot{|\!\Rrightarrow} \diamond (W \ast [\mathcal{E}_2]^{\gamma_{\mathrm{EN}}} \ast P), \qquad |\!\Rrightarrow_{\mathcal{E}} P \triangleq {}^{\mathcal{E}}|\!\Rrightarrow^{\mathcal{E}} P,
$$

$$
P \mathrel{{}^{\mathcal{E}_1}\!\!\Rrightarrow^{\mathcal{E}_2}} Q \triangleq \square (P \mathrel{-\!\!\ast} {}^{\mathcal{E}_1}|\!\Rrightarrow^{\mathcal{E}_2} Q), \qquad P \Rrightarrow_{\mathcal{E}} Q \triangleq P \mathrel{{}^{\mathcal{E}}\!\!\Rrightarrow^{\mathcal{E}}} Q .
$$

The modality satisfies: monotonicity; $\mathrm{True} \vdash {}^{\mathcal{E}_1}|\!\Rrightarrow^{\mathcal{E}_2}\, {}^{\mathcal{E}_2}|\!\Rrightarrow^{\mathcal{E}_1} \mathrm{True}$ when $\mathcal{E}_2 \subseteq \mathcal{E}_1$; ${}^{\mathcal{E}_1}|\!\Rrightarrow^{\mathcal{E}_2}\, {}^{\mathcal{E}_2}|\!\Rrightarrow^{\mathcal{E}_3} P \vdash {}^{\mathcal{E}_1}|\!\Rrightarrow^{\mathcal{E}_3} P$; $Q \ast {}^{\mathcal{E}_1}|\!\Rrightarrow^{\mathcal{E}_2} P \vdash {}^{\mathcal{E}_1 \uplus \mathcal{E}_f}|\!\Rrightarrow^{\mathcal{E}_2 \uplus \mathcal{E}_f} (Q \ast P)$; $\dot{|\!\Rrightarrow} P \vdash |\!\Rrightarrow_{\mathcal{E}} P$; and $\triangleright P \vdash |\!\Rrightarrow_{\mathcal{E}} P$ for timeless $P$.

## Depends on

- [World satisfaction](world-satisfaction.md)
- [Basic update modality](../iris-base-logic/basic-update-modality.md)
- [Except-0 modality and timeless propositions](../iris-base-logic/except-0-modality-and-timeless-propositions.md)
- [Iris base logic](../iris-base-logic/iris-base-logic.md)
- [Global ghost state and ghost ownership](../iris-base-logic/global-ghost-state-and-ghost-ownership.md)

## Proof depends on

- [World satisfaction](world-satisfaction.md)
- [Basic update modality](../iris-base-logic/basic-update-modality.md)
- [Except-0 modality and timeless propositions](../iris-base-logic/except-0-modality-and-timeless-propositions.md)
- [Iris base logic](../iris-base-logic/iris-base-logic.md)
- [Global ghost state and ghost ownership](../iris-base-logic/global-ghost-state-and-ghost-ownership.md)

## Expansion

The first mask says which invariants the modality may use and the second which remain enabled afterwards; masks are sugar for ownership of enabled tokens, which is why a mask may shrink and grow back without opening anything. Eliminating a mask-changing update in a goal changes only the goal's first mask. The fancy update is also expressible from view shifts as $\exists R.\ R \ast (R \mathrel{{}^{\mathcal{E}_1}\!\!\Rrightarrow^{\mathcal{E}_2}} P)$.

## Sources

- R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal and D. Dreyer, "Iris from the ground up: a modular foundation for higher-order concurrent separation logic", *Journal of Functional Programming* 28, e20, 2018, open access <https://doi.org/10.1017/S0956796818000151> (version of record, Cambridge University Press), Section 7.2, Figures 14-15 (fancy update, view shifts, FUP-MONO, FUP-INTRO-MASK, FUP-TRANS, FUP-FRAME, FUP-UPD, FUP-TIMELESS, FUP-CHANGE-MASK) and Section 8.1.
