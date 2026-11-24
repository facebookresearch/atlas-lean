# Nerve Data Simplicial Iso inv app

Backward component of `nerveDataSimplicialIso` is the identity.

Both sides act identically on every generator morphism, so the chosen
component iso is `Iso.refl _`. Consumers should rewrite with this lemma
rather than unfolding the multi-component iso construction.
