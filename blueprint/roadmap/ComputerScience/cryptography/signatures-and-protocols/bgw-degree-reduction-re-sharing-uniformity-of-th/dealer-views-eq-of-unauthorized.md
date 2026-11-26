# Re-shared subshares hide the values from small coalitions

Let `F` be a field and `Party` a finite type of parties with decidable
equality, with Shamir parameters `params` and a tail sampler `sampler`. If the
coalition `I` has at most `params.threshold` members, then `dealerViews params
sampler I h₁ = dealerViews params sampler I h₂` for all `h₁ h₂ : Party → F`,
with no agreement hypothesis. This concerns the received subshare matrix
alone, not its joint law with the coalition's original shares.
