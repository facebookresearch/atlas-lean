# Vc

Generate the assertion obligations `C.vc Q` for an annotated command
`C` and heap postcondition `Q`. Atomic commands impose no further obligations:
their memory-safety requirements are in `pre`. A sequence checks the first
command against the second command's precondition and checks the second
against `Q`; a conditional checks both branches against `Q`.

A loop requires its invariant and true guard to entail the body precondition
for that invariant, its invariant and false guard to entail `Q`, and the
body's own verification conditions. A frame requires `body.vc localPost`,
stability of `R` under store updates agreeing outside `body.strip.modVars`,
and `(localPost ⋆ R).Entails Q`.
