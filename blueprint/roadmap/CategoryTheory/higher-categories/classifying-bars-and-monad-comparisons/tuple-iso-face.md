# Tuple Iso face

Face compatibility of the degreewise equivalence.

After unfolding both isos to tuple functions, the zeroth face drops the head
(`Fin.tail`), the last face drops the tail, and interior faces multiply the
two adjacent entries in order. The `Gᵐᵒᵖ` order makes nerve composition agree
with bar multiplication via `SingleObj.comp_as_mul`; the bar side uses the
accepted `barFaceApp_of_val_zero/val_last/middle` with `tensorMonad_mu_app`.
