# Joint subshare law is determined by the per-dealer views

Let `F` be a field and `Party` a finite type of parties with decidable
equality, with Shamir parameters `params` and a tail sampler `sampler`. If,
for every dealer `i`, coalition `I`'s view distribution of the Shamir sharing
of `h₁ i` equals that of `h₂ i`, then `dealerViews params sampler I h₁ =
dealerViews params sampler I h₂`.
