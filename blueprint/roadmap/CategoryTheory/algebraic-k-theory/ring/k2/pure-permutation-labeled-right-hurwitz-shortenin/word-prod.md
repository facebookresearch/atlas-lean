# Word Prod

Head-left labeled word product: `[] ↦ 1`, `(l :: ws) ↦ swapDenote l *
wordProd ws`. Orientation is head-left throughout, matching the accepted
`List.ofFn`/`List.prod` word order. The empty word gives `1`. Purpose:
permutation product input. Nonclaims: no Weyl evaluation or Matsumoto claim.
