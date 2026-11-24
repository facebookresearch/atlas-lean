# Augmentation bridge right

Bridge: the endpoint augmentation followed by the unop-identification
equals `single₀UnopIso` followed by the unop'd op-side augmentation.

Informal sketch: degreewise (`Hom.ext`). In degree `0` everything is an
identity (`rfl`-bridges for `comp_f`/`unopFunctor`-`f`/`opFunctor`-`f` and
the `π`-unfolding, `unop_comp`, `(·.op).unop`, `single₀OpIso_hom_f_zero`);
off degree `0` both sides are maps out of a zero object
(`IsZero.eq_of_src`).
