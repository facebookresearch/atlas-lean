# Invariant access rule

An Iris invariant in namespace $\mathcal{N}$ can be opened by a fancy update that removes $\mathcal{N}$ from the mask and yields its content one step later, together with the obligation to restore the content before the mask is restored.

**Theorem.** For every proposition $P$, namespace $\mathcal{N}$ and mask $\mathcal{E}$:

- if $\mathcal{N}^{\uparrow} \subseteq \mathcal{E}$ then $\boxed{P}^{\mathcal{N}} \vdash {}^{\mathcal{E}}|\!\Rrightarrow^{\mathcal{E} \setminus \mathcal{N}^{\uparrow}} \big( \triangleright P \ast (\triangleright P \mathrel{-\!\!\ast} {}^{\mathcal{E} \setminus \mathcal{N}^{\uparrow}}|\!\Rrightarrow^{\mathcal{E}} \mathrm{True}) \big)$;
- $\triangleright P \vdash |\!\Rrightarrow_{\mathcal{E}} \boxed{P}^{\mathcal{N}}$;
- $\boxed{P}^{\mathcal{N}} \vdash \square \boxed{P}^{\mathcal{N}}$.

## Depends on

- [Fancy update modality](fancy-update-modality.md)
- [World satisfaction](world-satisfaction.md)

## Proof depends on

- [Fancy update modality](fancy-update-modality.md)
- [World satisfaction](world-satisfaction.md)

## Expansion

Opening a single invariant $\iota \in \mathcal{E}$, ${}^{\mathcal{E}}|\!\Rrightarrow^{\mathcal{E} \setminus \{\iota\}} (\triangleright P \ast [\{\iota\}]^{\gamma_{\mathrm{DIS}}})$, comes from splitting off the enabled token and the open/close law of world satisfaction; closing is the converse. The namespace version removes the rest of $\mathcal{N}^{\uparrow}$ from the mask without opening it, by mask introduction, and puts it back after closing (the derivation of Figure 16). Allocation uses the allocation law with the infinite set $\mathcal{N}^{\uparrow}$; persistence holds because registry fragments are their own cores.

## Sources

- R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal and D. Dreyer, "Iris from the ground up: a modular foundation for higher-order concurrent separation logic", *Journal of Functional Programming* 28, e20, 2018, open access <https://doi.org/10.1017/S0956796818000151> (version of record, Cambridge University Press), Section 7.2, Figure 15 (INV-ACCESS, INV-ALLOC, INV-PERSIST), Figure 16 and its derivation notes (INV-OPEN, INV-CLOSE).
