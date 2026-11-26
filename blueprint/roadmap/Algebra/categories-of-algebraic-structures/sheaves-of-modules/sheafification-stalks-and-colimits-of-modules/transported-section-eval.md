# Evaluation of a generator after further slice restriction

Let `(D,K)` be a site with pullbacks, `S : Sheaf K RingCat.{u}`, and additive sheafification
with the locally-bijective comparison on all slices. For a module sheaf `M`, a generating
family `G` of `M.over Y`, and `q : V → Y`, transport `G` along `overMap S q` and the canonical
comparison to `M.over V`. For `k∈G.I` and `U'∈(Over V)ᵒᵖ`, its generator value equals `(G.s
k).eval (op (Over.mk (U'.unop.hom ≫ q)))`: the source section evaluated on the composite arrow
to `Y`.
