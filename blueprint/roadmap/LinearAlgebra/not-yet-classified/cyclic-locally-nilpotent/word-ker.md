# Word Ker

The submodule of vectors killed by every composite `f i₁ ∘ ⋯ ∘ f i_d` of `d` members of a
family `f` of endomorphisms (`Module.End.mem_wordKer_iff`). Only `0` is killed by the empty
composite, and `x` is killed by all composites of length `d + 1` exactly when every `f i x` is
killed by all composites of length `d` (`Module.End.mem_wordKer_succ`).

These submodules increase with `d` (`Module.End.monotone_wordKer`). The family is *locally
nilpotent* when they exhaust the module, `⨆ d, wordKer f d = ⊤`: every vector is killed by all
sufficiently long composites (`Module.End.iSup_wordKer_eq_top_iff`).
