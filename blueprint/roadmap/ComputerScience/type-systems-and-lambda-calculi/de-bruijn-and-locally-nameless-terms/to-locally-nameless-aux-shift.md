# Shifting below the cutoff is invisible

If `t` is scoped at `cutoff + names.length`, then
translating `shift amount cutoff t` under `amount + cutoff` binders gives the translation of `t`
under `cutoff` binders.
