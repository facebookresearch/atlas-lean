# PRF-MAC forgery is invariant under relabeling messages along an injection

Let the key space `K` be finite and nonempty and the messages `M` have
decidable equality; the forger's coins are arbitrary. Let `M'` and the tags `T`
have decidable equality, `G : K → M' → T` and `e : M → M'` injective. For
every forger `A`, the forgery experiment of `prfMac G` against `A` relabeled
along `e` equals the forgery experiment of `prfMac (fun k m => G k (e m))`
against `A`; freshness of the forged message is preserved because `e` is
injective.
