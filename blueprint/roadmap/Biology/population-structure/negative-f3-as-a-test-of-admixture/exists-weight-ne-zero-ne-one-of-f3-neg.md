# Exists weight ne zero ne one of f3 neg

Sufficiency of a negative `f3`, target form, in a general drift model: if
the source weights of `A` and `B` lie in `[0, 1]` and `f3 C A B < 0`, then the
target `C` itself has a lineage weight that is neither `0` nor `1` (so `C`
does not have the binary weights of an unadmixed population). The
admixture-graph form is `AdmixtureGraph.exists_weight_ne_zero_ne_one_of_f3_neg`;
this is the contrapositive of `DriftModel.f3_nonneg_of_binary_target`. Only the
sources' weights are assumed in `[0, 1]`; no range assumption on `C` is needed.
