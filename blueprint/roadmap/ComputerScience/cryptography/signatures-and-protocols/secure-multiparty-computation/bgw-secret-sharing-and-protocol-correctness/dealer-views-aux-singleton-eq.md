# A single dealer reveals nothing to an unauthorized coalition

Let `F` be a field and `Party` a finite type of parties with decidable
equality, with Shamir parameters `params` and a tail sampler `sampler`. If the
coalition `I` is not authorized, then for any `h₁ h₂ : Party → F`, any dealer
`i` and any base matrix `g`, the one-dealer joint distribution
`dealerViewsAux` over `[i]` built from the Shamir views of `h₁ j` equals the
one built from the Shamir views of `h₂ j`.
